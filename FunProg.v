Require Import SLFun.Util.

Require Import Coq.Setoids.Setoid.


Module Spec. Section Spec.
  Local Set Implicit Arguments.
  Variable A : Type.

  Definition wp_t := forall (post : A -> Prop), Prop.

  Definition monotone (wp : wp_t) : Prop :=
    forall (post0 post1 : A -> Prop) (LE : forall x, post0 x -> post1 x),
    wp post0 -> wp post1.

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
    Variable P : TF.p.

    Local Set Implicit Arguments.
    Record t := mk {
      v_val : p_val P;
      v_sel : Tuple.t (p_sel P v_val);
    }.
    Local Unset Implicit Arguments.

    Definition all (f : t -> Prop) :=
      forall (v : p_val P), Tuple.all (p_sel P v) (fun sels => f (mk v sels)).

    Lemma all_iff f:
      all f <-> forall x : t, f x.
    Proof.
      unfold all; setoid_rewrite Tuple.all_iff.
      split; auto.
      intros H []; apply H.
    Qed.

    Definition ex (f : t -> Prop) :=
      exists (v : p_val P), Tuple.ex (p_sel P v) (fun sels => f (mk v sels)).

    Lemma ex_iff f:
      ex f <-> exists x : t, f x.
    Proof.
      unfold ex; setoid_rewrite Tuple.ex_iff.
      split; intro H; repeat destruct H; eauto.
      destruct x; eauto.
    Qed.
  End Values.
  
  Definition unit : p := mk_p unit (fun _ => nil).
  Definition tt : t unit := mk unit tt tt.
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
