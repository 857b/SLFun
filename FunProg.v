Require Import SLFun.Util.

Require Import Coq.Setoids.Setoid.


(* Type family *)
Module TF.
  Record p := mk_p {
    p_val : Type;
    p_sel : p_val -> list Type;
  }.

  Section Values.
    Context [P : TF.p].

    Record t := mk_v {
      v_val : p_val P;
      v_sel : Tuple.t (p_sel P v_val);
    }.

    Definition arrow (TRG : t -> Type) : Type :=
      forall (val : p_val P), Tuple.arrow (p_sel P val) (fun sel => TRG (mk_v val sel)).

    Definition arrow_of_fun [TRG : t -> Type] (f : forall x : t, TRG x) : arrow TRG :=
      fun val => Tuple.arrow_of_fun (fun sel => f (mk_v val sel)).

    Definition arrow_to_fun [TRG : t -> Type] (f : arrow TRG) (x : t): TRG x.
    Proof.
      case x as [val sel].
      exact (Tuple.arrow_to_fun (f val) sel).
    Defined.

    Lemma arrow_to_of [TRG : t -> Type] (f : forall x : t, TRG x) (x : t):
      arrow_to_fun (arrow_of_fun f) x = f x.
    Proof.
      case x as []; refine (Tuple.arrow_to_of _ _).
    Qed.

    Definition all (f : t -> Prop) :=
      forall (v : p_val P), Tuple.all (p_sel P v) (fun sels => f (mk_v v sels)).

    Lemma all_iff f:
      all f <-> forall x : t, f x.
    Proof.
      unfold all; setoid_rewrite Tuple.all_iff.
      split; auto.
      intros H []; apply H.
    Qed.

    Definition ex (f : t -> Prop) :=
      exists (v : p_val P), Tuple.ex (p_sel P v) (fun sels => f (mk_v v sels)).

    Lemma ex_iff f:
      ex f <-> exists x : t, f x.
    Proof.
      unfold ex; setoid_rewrite Tuple.ex_iff.
      split; intro H; repeat destruct H; eauto.
      destruct x; eauto.
    Qed.
  End Values.
  Global Arguments t : clear implicits.
  Global Arguments mk_v : clear implicits.
  Global Arguments arrow : clear implicits.
  Global Arguments all : clear implicits.
  Global Arguments ex : clear implicits.
  
  Global Arguments arrow !P _/.
  Global Arguments arrow_of_fun !P _ _/.
  Global Arguments all !P _/.
  Global Arguments ex  !P _/.


  Definition mk [p_val] (p_sel : p_val -> list Type)
    (v_val : p_val) (v_sel : Tuple.t (p_sel v_val)) : t (mk_p p_val p_sel)
    := mk_v (mk_p p_val p_sel) v_val v_sel.
  
  Definition unit : p := mk_p unit (fun _ => nil).
  Definition tt : t unit := mk_v unit tt tt.
End TF.

Module Spec.
  Local Set Implicit Arguments.
  Section WLP.
    Variable A : Type.

    Definition post_t := A -> Prop.
    Definition wp_t   := post_t -> Prop.

    Definition monotone (wp : wp_t) : Prop :=
      forall (post0 post1 : post_t) (LE : forall x, post0 x -> post1 x),
      wp post0 -> wp post1.

    Lemma wp_morph (wp : wp_t) (MONO : monotone wp) (post0 post1 : post_t)
      (POST : forall x, post0 x <-> post1 x):
      wp post0 <-> wp post1.
    Proof.
      split; apply MONO, POST.
    Qed.

    Definition wp_eq (wp0 wp1 : wp_t) : Prop :=
      forall post : post_t, wp0 post <-> wp1 post.

    Global Instance wp_eq_Equivalence : Equivalence wp_eq.
    Proof.
      apply Equivalence.pointwise_equivalence, iff_equivalence.
    Qed.
  End WLP.

  Record t (A : TF.p) := {
    pre  : Prop;
    post : TF.arrow A (fun _ => Prop);
  }.
End Spec.


Definition instr (A : TF.p) : Type := {wp : Spec.wp_t (TF.t A) | Spec.monotone wp}.
Definition wlp [A : TF.p] (i : instr A) : Spec.wp_t (TF.t A)
  := proj1_sig i.
Definition wlp_monotone [A : TF.p] (i : instr A) : Spec.monotone (wlp i)
  := proj2_sig i.

Definition eqv [A : TF.p] (p0 p1 : instr A) : Prop :=
  Spec.wp_eq (wlp p0) (wlp p1).

Global Instance eqv_Equivalence A : Equivalence (@eqv A).
Proof.
  Rel.by_expr (Rel.pull (@wlp A) (@Spec.wp_eq _)).
Qed.

Inductive wlpA [A : TF.p] (i : instr A) (post : TF.arrow A (fun _ => Prop)) : Prop :=
  wlpA_I (P : wlp i (TF.arrow_to_fun post)).


Section Instr.
  Local Obligation Tactic := cbn; intros; do 3 intro; try solve [intuition auto].

  Program Definition Ret [A : TF.p] (x : TF.t A) : instr A
    := fun post => post x.

  Program Definition Bind [A B : TF.p] (f : instr A) (g : TF.arrow A (fun _ => instr B)) : instr B
    := fun post => wlp f (fun x => wlp (TF.arrow_to_fun g x) post).
  Next Obligation.
    apply wlp_monotone; intro; apply wlp_monotone, LE.
  Qed.

  Program Definition Call [A : TF.p] (s : Spec.t A) : instr A
    := fun post => Spec.pre s /\ forall x : TF.t A, TF.arrow_to_fun (Spec.post s) x -> post x.

  Program Definition Assert (P : Prop) : instr TF.unit
    := fun post => P /\ post TF.tt.
End Instr.

Inductive wlp_formula [A : TF.p] (i : instr A) (f : forall post : TF.t A -> Prop, Prop) : Prop :=
  wlp_formulaI (F : forall post, f post -> wlp i post).

Section WLP_Formula.
  Lemma wlp_formulaE [A i f post] (H : @wlp_formula A i f) (F : f post): wlp i post.
  Proof.
    case H; auto.
  Qed.

  Lemma wlp_formula_imp [A i] f0 [f1 : _ -> Prop]
    (F : wlp_formula i f0)
    (M : forall post, f1 post -> f0 post):
    @wlp_formula A i f1.
  Proof.
    constructor; intros.
    apply F; auto.
  Qed.

  Lemma wlp_formula_def [A] i:
    @wlp_formula A i (wlp i).
  Proof.
    constructor; auto.
  Qed.

  Lemma wlp_formula_Bind [A B f g ff fg]
    (Ff : wlp_formula f ff)
    (Fg : TF.arrow A (fun x => wlp_formula (TF.arrow_to_fun g x) (TF.arrow_to_fun fg x))):
    wlp_formula (@Bind A B f g)
      (fun post => ff (fun x => TF.arrow_to_fun fg x post)).
  Proof.
    constructor.
    intros post HF%(wlp_formulaE Ff); simpl.
    eapply wlp_monotone, HF; simpl.
    intros x HG%(wlp_formulaE (TF.arrow_to_fun Fg x)).
    exact HG.
  Qed.

  Lemma wlp_formula_Call [A] s:
    wlp_formula (@Call A s)
      (fun post => Spec.pre s /\ TF.all A (fun x => TF.arrow_to_fun (Spec.post s) x -> post x)).
  Proof.
    constructor; setoid_rewrite TF.all_iff; auto.
  Qed.
End WLP_Formula.

(* build a formula [match x with ... end] *)
Ltac build_wlp_formula_match build_f x :=
  lazymatch goal with |- wlp_formula _ ?f =>
  Tac.build_term f ltac:(fun _ => intro (* post *); destruct x; try clear x; shelve);
  destruct x; build_f
  end.

(* destructive let *)
Ltac build_wlp_formula_dlet build_f x :=
  simple refine (wlp_formula_imp _ _ _);
  [ (* f0 *) destruct x; shelve
  | (* F  *) destruct x; build_f
  | (* M  *)
    intro (* post *);
    let f := fresh "f" in intro f;
    case_eq x;
    exact f ].

(* changes an hypothesis [H : H0 /\ ... /\ H9 /\ L] into [H : L] *)
Ltac conj_proj_last H :=
  repeat lazymatch goal with
  | H : _ /\ _ |- _ => apply proj2 in H
  end.

Ltac build_wlp_formula_branch build_f x :=
  simple refine (wlp_formula_imp _ _ _);
  [ (* f0 *) destruct x; try clear x; shelve
  | (* F  *) destruct x; build_f
  | (* M  *)
    cbn;
    intro (* post *);
    let f := fresh "f" in intro f;
    case_eq x;
    [ (cbn in f; conj_proj_last f; eapply proj1 in f; exact f) ..
    | cbn in f; conj_proj_last f; exact f] ].

(* solves a goal [wlp_formula i ?f] *)
Ltac build_wlp_formula_ dmatch :=
  let rec build :=
  cbn;
  lazymatch goal with
  | |- wlp_formula (Ret _) _ =>
      refine (wlp_formula_def _)
  | |- wlp_formula (Bind _ _) _ =>
      refine (wlp_formula_Bind _ _);
      [ build | cbn; repeat intro; build ]
  | |- wlp_formula (Call _) _ =>
      refine (wlp_formula_Call _)
  | |- wlp_formula (Assert _) _ =>
      refine (wlp_formula_def _)
  | |- wlp_formula (match ?x with _ => _ end) _ =>
      lazymatch dmatch with
      | true =>
          tryif (try (case x; [ (* one case *) ]; fail 1))
          then build_wlp_formula_branch build x
          else build_wlp_formula_dlet   build x
      | false =>
          build_wlp_formula_match build x
      end
  | |- ?g => fail "build_wlp_formula: " g
  end
  in build.

Ltac build_wlp_formula := build_wlp_formula_ true.

Local Lemma by_wlp_lem [pre : Prop] [A] [i : instr A] [post f]
  (F : wlp_formula i f)
  (C : pre -> f (TF.arrow_to_fun post))
  (P : pre): wlpA i post.
Proof.
  constructor; case F as [F].
  apply F, C, P.
Qed.

Ltac by_wlp_ dmatch :=
  refine (by_wlp_lem _ _);
  [ build_wlp_formula_ dmatch | cbn].

Ltac by_wlp := by_wlp_ true.
