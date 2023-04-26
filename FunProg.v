Require Import SLFun.Util.

Require Import Coq.Setoids.Setoid.


Module Spec. Section Spec.
  Local Set Implicit Arguments.
  Variable A : Type.

  Definition wp_t := forall (post : A -> Prop), Prop.

  Definition monotone (wp : wp_t) : Prop :=
    forall (post0 post1 : A -> Prop) (LE : forall x, post0 x -> post1 x),
    wp post0 -> wp post1.

  Lemma wp_morph (wp : wp_t) (MONO : monotone wp) (post0 post1 : A -> Prop)
    (POST : forall x : A, post0 x <-> post1 x):
    wp post0 <-> wp post1.
  Proof.
    split; apply MONO, POST.
  Qed.

  Definition wp_eq (wp0 wp1 : wp_t) : Prop :=
    forall post : A -> Prop, wp0 post <-> wp1 post.

  Global Instance wp_eq_Equivalence : Equivalence wp_eq.
  Proof.
    apply Equivalence.pointwise_equivalence, iff_equivalence.
  Qed.

  Record t := {
    pre  : Prop;
    post : A -> Prop;
  }.
End Spec. End Spec.

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

Inductive instr : TF.p -> Type :=
  | Ret [A] (x : TF.t A) : instr A
  | Bind [A B] (f : instr A) (g : TF.t A -> instr B) : instr B
  | Call [A] (s : Spec.t (TF.t A)) : instr A
  | Assert (P : Prop) : instr TF.unit.

Fixpoint wlp [A : TF.p] (i : instr A) : Spec.wp_t (TF.t A) :=
  match i with
  | Ret x     => fun post => post x
  | Bind f g  => fun post => wlp f (fun x => wlp (g x) post)
  | @Call A s => fun post => Spec.pre s /\ TF.all A (fun x => Spec.post s x -> post x)
  | Assert P  => fun post => P /\ post TF.tt
  end.

Lemma wlp_monotone A i : Spec.monotone (@wlp A i).
Proof.
  induction i; do 3 intro; simpl; try solve [intuition auto].
  - (* Bind *)
    apply IHi; intro x; apply (H x), LE.
  - (* Call *)
    rewrite !TF.all_iff; intuition.
Qed.

Definition eqv [A : TF.p] (p0 p1 : instr A) : Prop :=
  Spec.wp_eq (wlp p0) (wlp p1).

Global Instance eqv_Equivalence A : Equivalence (@eqv A).
Proof.
  Rel.by_expr (Rel.pull (@wlp A) (@Spec.wp_eq _)).
Qed.


Definition wlpA [A : TF.p] (i : instr A) (post : TF.arrow A (fun _ => Prop)) : Prop :=
  wlp i (TF.arrow_to_fun post).

Definition BindA [A B : TF.p] (f : instr A) (g : TF.arrow A (fun _ => instr B)) : instr B :=
  @Bind A B f (TF.arrow_to_fun g).

Global Arguments BindA : simpl never.
