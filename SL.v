Require Import SLFun.Values.

Require Import Coq.Setoids.Setoid.

Declare Scope slprop_scope.
Delimit Scope slprop_scope with slprop.

(* [FMem] *)

Module FCell.

  Definition t := option memdata.

  Definition emp : t := None.

  Definition join (c0 c1 : t) : option t :=
    match c0, c1 with
    | Some v, None | None, Some v => Some (Some v)
    | None, None => Some None
    | Some _, Some _ => None
    end.

  Lemma join_comm c0 c1:
    join c0 c1 = join c1 c0.
  Proof.
    case c0, c1; reflexivity.
  Qed.

  Lemma join_assoc [c0 c1 c2 c01 c012]:
    join c0  c1 = Some c01  ->
    join c01 c2 = Some c012 ->
    exists c12,
      join c1 c2  = Some c12 /\
      join c0 c12 = Some c012.
  Proof.
    destruct c0, c1, c2; do 2 first [discriminate 1 | injection 1 as <-];
    repeat esplit.
  Qed.

  Lemma join_emp_l c:
    join emp c = Some c.
  Proof.
    case c; reflexivity.
  Qed.
  
  Lemma join_emp_r c:
    join c emp = Some c.
  Proof.
    case c; reflexivity.
  Qed.

End FCell.

Module FMem.
  
  Definition t := ptr -> FCell.t.

  Definition eq : relation t :=
    Morphisms.pointwise_relation ptr Logic.eq.

  Definition emp : t := fun _ => FCell.emp.

  Definition is_join (m m0 m1 : t) : Prop :=
    forall p : ptr, FCell.join (m0 p) (m1 p) = Some (m p).

  Global Add Morphism is_join
    with signature eq ==> eq ==> eq ==> iff
    as is_join_morph.
  Proof.
    intros ? ? E ? ? E0 ? ? E1; unfold is_join.
    apply Morphisms_Prop.all_iff_morphism; intro.
    rewrite E, E0, E1.
    reflexivity.
  Qed.

  Lemma is_join_comm m m0 m1:
    is_join m m0 m1 <-> is_join m m1 m0.
  Proof.
    unfold is_join.
    setoid_rewrite FCell.join_comm at 1.
    reflexivity.
  Qed.

  Lemma is_join_assoc [m0 m1 m2 m01 m012]
    (J0 : is_join m01  m0  m1)
    (J1 : is_join m012 m01 m2):
    exists m12,
      is_join m12  m1 m2 /\
      is_join m012 m0 m12.
  Proof.
    exists (fun p => match FCell.join (m1 p) (m2 p) with
                     | Some c => c
                     | None   => FCell.emp (* placeholder *)
                     end).
    refine ((fun P => conj (fun p => proj1 (P p)) (fun p => proj2 (P p))) _).
    intro p.
    ecase (FCell.join_assoc (J0 p) (J1 p)) as (? & -> & ->).
    repeat esplit.
  Qed.

  Lemma is_join_emp_l m m0:
    is_join m emp m0 <-> eq m m0.
  Proof.
    unfold is_join, emp.
    setoid_rewrite FCell.join_emp_l.
    apply Morphisms_Prop.all_iff_morphism; intro.
    split; congruence.
  Qed.

  Lemma is_join_emp_r m m0:
    is_join m m0 emp <-> eq m m0.
  Proof.
    rewrite is_join_comm.
    apply is_join_emp_l.
  Qed.

End FMem.

(* [SLprop] *)

Lemma pull_Equivalence [A B] (f : A -> B) (R : relation B) (E : Equivalence R):
  Equivalence (fun x y => R (f x) (f y)).
Proof.
  constructor; repeat intro.
  - reflexivity.
  - symmetry; auto.
  - etransitivity; eauto.
Qed.

Module SLprop.
  
  Record t := mk_sl_pred {
    sl_pred :> FMem.t -> Prop;
    sl_wf   : forall m0 m1 (MEQ : FMem.eq m0 m1) (HM0 : sl_pred m0), sl_pred m1;
  }.

  Bind Scope slprop_scope with t.

  Definition eq (h0 h1 : t) : Prop :=
    Morphisms.pointwise_relation FMem.t iff h0 h1.

  Global Instance eq_Equivalence : Equivalence eq.
  Proof.
    apply (pull_Equivalence sl_pred).
    auto with typeclass_instances.
  Qed.

  Global Add Morphism sl_pred
    with signature eq ==> FMem.eq ==> iff
    as sl_pred_morph.
  Proof.
    intros h0 h1 EH m0 m1 EM; etransitivity.
    + apply EH.
    + split; apply h1.(sl_wf); [|symmetry]; exact EM.
  Qed.

  Definition imp (h0 h1 : t) : Prop :=
    forall m, h0 m -> h1 m.

  Global Instance imp_PreOrder : PreOrder imp.
  Proof.
    split.
    - intros ? ?; auto.
    - intros ? ? ? H0 H1 m; specialize (H0 m); specialize (H1 m); tauto.
  Qed.

  Global Add Morphism imp
    with signature eq ==> eq ==> iff
    as imp_morph.
  Proof.
    unfold imp.
    intros ? ? E0 ? ? E1.
    setoid_rewrite E0.
    setoid_rewrite E1.
    reflexivity.
  Qed.

  Lemma eq_iff_imp h0 h1:
    eq h0 h1 <-> (imp h0 h1 /\ imp h1 h0).
  Proof.
    split.
    - intro E; split; intro m; apply (E m).
    - intros E m; split; apply E.
  Qed.


  Program Definition emp : t :=
    mk_sl_pred (fun m => FMem.eq m FMem.emp) _.
  Next Obligation.
    rewrite <- MEQ; assumption.
  Qed.

  Program Definition pure (p : Prop) : t :=
    mk_sl_pred (fun m => FMem.eq m FMem.emp /\ p) _.
  Next Obligation.
    rewrite <- MEQ; tauto.
  Qed.

  Program Definition star (h0 h1 : t) : t :=
    mk_sl_pred (fun m => exists m0 m1, FMem.is_join m m0 m1 /\ h0 m0 /\ h1 m1) _.
  Next Obligation.
    setoid_rewrite <- MEQ; eauto.
  Qed.

  Module Notations.
    Infix "**" := star (at level 80, right associativity) : slprop_scope.
  End Notations.
  Import Notations.

  Lemma star_morph_imp [h0 h0' h1 h1']
    (H0 : imp h0 h0')
    (H1 : imp h1 h1'):
    imp (h0 ** h1) (h0' ** h1').
  Proof.
    intros m (m0 & m1 & ? & ? & ?).
    specialize (H0 m0). specialize (H1 m1).
    exists m0, m1. tauto.
  Qed.

  Global Add Morphism star
    with signature eq ==> eq ==> eq
    as star_morph_eq.
  Proof.
    setoid_rewrite eq_iff_imp.
    intros ? ? (E0 & E1) ? ? (E2 & E3).
    split; apply star_morph_imp; assumption.
  Qed.

  Lemma star_comm h0 h1:
    eq (h0 ** h1) (h1 ** h0).
  Proof.
    intro m; simpl.
    setoid_rewrite FMem.is_join_comm at 1.
    split; intros (m0 & m1 & ? & ? & ?); exists m1, m0; eauto.
  Qed.

  Lemma star_assoc_imp h0 h1 h2:
    imp ((h0 ** h1) ** h2) (h0 ** (h1 ** h2)).
  Proof.
    intros m (m01 & m2 & J0 & (m0 & m1 & J1 & H0 & H1) & H2).
    case (FMem.is_join_assoc J1 J0) as (m12 & ? & ?).
    exists m0, m12; repeat (split; try assumption).
    exists m1, m2; tauto.
  Qed.

  Lemma star_assoc h0 h1 h2:
    eq ((h0 ** h1) ** h2) (h0 ** (h1 ** h2)).
  Proof.
    split. apply star_assoc_imp.
    intro H.
    rewrite (star_comm h0), (star_comm h1) in H.
    apply star_assoc_imp in H.
    rewrite (star_comm h2), (star_comm h1) in H.
    exact H.
  Qed.

  Lemma star_emp_l h:
    eq (emp ** h) h.
  Proof.
    intro m; simpl.
    split.
    - intros (m0 & m1 & J & E & H).
      rewrite E, FMem.is_join_emp_l in J.
      rewrite J.
      apply H.
    - intro H.
      exists FMem.emp, m.
      rewrite FMem.is_join_emp_l.
      intuition reflexivity.
  Qed.

  Lemma star_emp_r h:
    eq (h ** emp) h.
  Proof.
    rewrite star_comm.
    apply star_emp_l.
  Qed.

End SLprop.

Module SLNotations.
  Include SLprop.Notations.
  Bind Scope slprop_scope with SLprop.t.
  Coercion SLprop.sl_pred : SLprop.t >-> Funclass.
End SLNotations.
