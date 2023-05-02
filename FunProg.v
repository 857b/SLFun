Require Import SLFun.Util.

Require Import Coq.Setoids.Setoid.


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

  Record t (A : DTuple.p) := {
    pre  : Prop;
    post : DTuple.arrow A (fun _ => Prop);
  }.
End Spec.


Definition instr (A : DTuple.p) : Type := {wp : Spec.wp_t (DTuple.t A) | Spec.monotone wp}.
Definition wlp [A : DTuple.p] (i : instr A) : Spec.wp_t (DTuple.t A)
  := proj1_sig i.
Definition wlp_monotone [A : DTuple.p] (i : instr A) : Spec.monotone (wlp i)
  := proj2_sig i.

Definition eqv [A : DTuple.p] (p0 p1 : instr A) : Prop :=
  Spec.wp_eq (wlp p0) (wlp p1).

Global Instance eqv_Equivalence A : Equivalence (@eqv A).
Proof.
  Rel.by_expr (Rel.pull (@wlp A) (@Spec.wp_eq _)).
Qed.

Inductive wlpA [A : DTuple.p] (i : instr A) (post : DTuple.arrow A (fun _ => Prop)) : Prop :=
  wlpA_I (P : wlp i (DTuple.to_fun post)).


Section Instr.
  Local Obligation Tactic := cbn; intros; do 3 intro; try solve [intuition auto].

  Program Definition Ret [A : DTuple.p] (x : DTuple.t A) : instr A
    := fun post => post x.

  Program Definition Bind [A B : DTuple.p] (f : instr A) (g : DTuple.arrow A (fun _ => instr B)) : instr B
    := fun post => wlp f (fun x => wlp (DTuple.to_fun g x) post).
  Next Obligation.
    apply wlp_monotone; intro; apply wlp_monotone, LE.
  Qed.

  Program Definition Call [A : DTuple.p] (s : Spec.t A) : instr A
    := fun post => Spec.pre s /\ forall x : DTuple.t A, DTuple.to_fun (Spec.post s) x -> post x.

  Program Definition Assert (P : Prop) : instr DTuple.unit
    := fun post => P /\ post DTuple.tt.
End Instr.

Inductive wlp_formula [A : DTuple.p] (i : instr A) (f : forall post : DTuple.t A -> Prop, Prop) : Prop :=
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
    (Fg : DTuple.arrow A (fun x => wlp_formula (DTuple.to_fun g x) (DTuple.to_fun fg x))):
    wlp_formula (@Bind A B f g)
      (fun post => ff (fun x => DTuple.to_fun fg x post)).
  Proof.
    constructor.
    intros post HF%(wlp_formulaE Ff); simpl.
    eapply wlp_monotone, HF; simpl.
    intros x HG%(wlp_formulaE (DTuple.to_fun Fg x)).
    exact HG.
  Qed.

  Lemma wlp_formula_Call [A] s:
    wlp_formula (@Call A s)
      (fun post => Spec.pre s /\ DTuple.all A (fun x => DTuple.to_fun (Spec.post s) x -> post x)).
  Proof.
    constructor; setoid_rewrite DTuple.all_iff; auto.
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
  (C : pre -> f (DTuple.to_fun post))
  (P : pre): wlpA i post.
Proof.
  constructor; case F as [F].
  apply F, C, P.
Qed.

Ltac by_wlp_ dmatch :=
  refine (by_wlp_lem _ _);
  [ build_wlp_formula_ dmatch | cbn].

Ltac by_wlp := by_wlp_ true.
