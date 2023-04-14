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

  Definition build_join
    (m0 m1 : t)
    (H : forall p, FCell.join (m0 p) (m1 p) <> None):
    exists m : t, is_join m m0 m1.
  Proof.
    exists (fun p =>
      match FCell.join (m0 p) (m1 p) with
      | Some c => c
      | None   => FCell.emp (* placeholder *)
      end).
    intro p; specialize (H p).
    destruct FCell.join; congruence.
  Qed.
  
  Definition cell (p : ptr) (d : memdata) : t :=
    fun r => if Mem.ptr_eq r p then Some d else None.

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

  Lemma sl_pred_eq (h0 h1 : t) (m : FMem.t)
    (E : eq h0 h1):
    h0 m <-> h1 m.
  Proof.
    rewrite E; reflexivity.
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

  (* [emp] *)

  Program Definition emp : t :=
    mk_sl_pred (fun m => FMem.eq m FMem.emp) _.
  Next Obligation.
    rewrite <- MEQ; assumption.
  Qed.

  (* [star] *)

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
  

  (* [pure] *)

  Program Definition pure (p : Prop) : t :=
    mk_sl_pred (fun m => FMem.eq m FMem.emp /\ p) _.
  Next Obligation.
    rewrite <- MEQ; tauto.
  Qed.

  Lemma star_pure (P : Prop) (h : t) (m : FMem.t):
    sl_pred (pure P ** h) m <-> P /\ h m.
  Proof.
    split.
    - intros (? & ? & J & (EMP & HP) & H).
      rewrite EMP, FMem.is_join_emp_l in J.
      rewrite <- J in H.
      auto.
    - intros (? & ?).
      exists FMem.emp, m; simpl; intuition.
      apply FMem.is_join_emp_l; reflexivity.
  Qed.

  Lemma pure_star_pure (P Q : Prop):
    eq (pure P ** pure Q) (pure (P /\ Q)).
  Proof.
    split.
    - intros (? & ? & J & (E0 & ?) & (E1 & ?)).
      rewrite E0, E1, FMem.is_join_emp_l in J.
      simpl; auto.
    - intros (E & (? & ?)).
      exists FMem.emp, FMem.emp; simpl; intuition.
      apply FMem.is_join_emp_l, E.
  Qed.

  Lemma imp_pure_l (P : Prop) (h0 h1 : t)
    (C : P -> imp h0 h1):
    imp (pure P ** h0) h1.
  Proof.
    intros m H%star_pure. case H as [].
    apply C; auto.
  Qed.

  Lemma imp_pure_r (P : Prop) (h0 h1 : SLprop.t)
    (HP : P)
    (C : imp h0 h1):
    imp h0 (pure P ** h1).
  Proof.
    intros m H0%C.
    apply star_pure; auto.
  Qed.


  (* cell: points to *)

  Program Definition cell (p : ptr) (d : memdata) : t :=
    mk_sl_pred (fun m => p <> NULL /\ FMem.eq m (FMem.cell p d)) _.
  Next Obligation.
    rewrite <- MEQ; auto.
  Qed.

  (* True *)

  Program Definition True : t :=
    mk_sl_pred (fun _ => Logic.True) _.

  (* Normalisation tactic *)

  Module Norm.
    Inductive reified :=
      | REmp
      | RPure (P : Prop)
      | RStar (h0 h1 : reified)
      | RAtom (h : t).

    Fixpoint reflect (h : reified) : t :=
      match h with
      | REmp        => emp
      | RPure P     => pure P
      | RStar h0 h1 => reflect h0 ** reflect h1
      | RAtom h     => h
      end.

    Ltac reify_core h :=
      match h with
      | emp          => exact REmp
      | pure ?P      => exact (RPure P)
      | star ?h0 ?h1 => refine (RStar _ _); [reify_core h0 | reify_core h1]
      | ?h           => exact (RAtom h)
      end.
    
    (* add an hypothesis [reflect r = h] to the goal *)
    Ltac reify h :=
      let R := fresh "Reified" in
      unshelve eassert (reflect _ = h) as R;
      [ reify_core h | reflexivity | revert R ].


    Definition r_rewrite_two (h0 h1 : reified) : reified :=
      match h0, h1 with
      | REmp, h | h, REmp => h
      | RPure P, RPure Q  => RPure (P /\ Q)
      | h0, RPure P       => RStar (RPure P) h0
      | h0, h1            => RStar h0 h1
      end.

    Lemma r_rewrite_two_correct h0 h1:
      eq (reflect (r_rewrite_two h0 h1)) (reflect h0 ** reflect h1).
    Proof.
      case h0, h1; simpl; symmetry; try reflexivity;
        auto using star_emp_l, star_emp_r, star_comm, pure_star_pure.
    Qed.

    Definition r_rewrite_head (h : reified) : reified :=
      match h with
      | RStar h0 (RStar h1 h2) =>
          match r_rewrite_two h0 h1 with
          | RStar h0 h1 => RStar h0 (RStar h1 h2)
          | h           => RStar h h2
          end
      | RStar h0 h1 => r_rewrite_two h0 h1
      | h => h
      end.

    Lemma r_rewrite_head_correct h:
      eq (reflect (r_rewrite_head h)) (reflect h).
    Proof.
      case h; simpl; try reflexivity.
      intros h0 []; simpl; try apply r_rewrite_two_correct.
      specialize (r_rewrite_two_correct h0 h1).
      destruct r_rewrite_two; simpl; try solve [intros ->; apply star_assoc].
      rewrite <- star_assoc; intros ->; rewrite star_assoc; reflexivity.
    Qed.

    Fixpoint r_rewrite_flat (h : reified) (acc : reified) {struct h} : reified :=
      match h with
      | RStar h0 h1 => r_rewrite_flat h0 (r_rewrite_flat h1 acc)
      | h => r_rewrite_head (RStar h acc)
      end.

    Lemma r_rewrite_flat_correct h acc:
      eq (reflect (r_rewrite_flat h acc)) (reflect h ** reflect acc).
    Proof.
      revert acc; induction h; intro; try solve [apply r_rewrite_head_correct].
      simpl; rewrite IHh1, IHh2, star_assoc; reflexivity.
    Qed.

    Definition r_normalize h :=
      r_rewrite_flat h REmp.

    Lemma r_normalize_correct h:
      eq (reflect (r_normalize h)) (reflect h).
    Proof.
      unfold r_normalize.
      rewrite r_rewrite_flat_correct.
      apply star_emp_r.
    Qed.

    Local Lemma normalize_r_eq r h:
      reflect r = h ->
      eq h (reflect (r_normalize r)).
    Proof.
      intros <-. rewrite r_normalize_correct. reflexivity.
    Qed.

    (* Solve a goal [h = ?h] *)
    Ltac normalize_core :=
      match goal with
      | |- eq ?h _ =>
          let R := fresh "R" in
          reify h; intro R;
          apply normalize_r_eq in R; cbn in R;
          exact R
      end.

    Ltac normalize :=
      match goal with
      | |- eq _ ?h =>
          first [
            is_evar h; normalize_core
          | etransitivity; [normalize_core|etransitivity; [|symmetry;normalize_core]]]
      | |- sl_pred _ _ =>
          eapply sl_pred_eq; [normalize_core|]
      | |- imp _ _ =>
          eapply imp_morph; [normalize_core|normalize_core|]
      | |- _ = _ => reflexivity
      end.

    Local Lemma test_normalize_0 h:
      eq (emp ** h) (h ** emp).
    Proof.
      normalize. reflexivity.
    Qed.
    
    Local Lemma test_normalize_1 h P Q:
      eq (pure P ** emp ** h ** pure Q) (h ** pure (P /\ Q) ** emp).
    Proof.
      normalize. reflexivity.
    Qed.

  End Norm.
  
  Ltac normalize := Norm.normalize.

End SLprop.

Module SLNotations.
  Include SLprop.Notations.
  Bind Scope slprop_scope with SLprop.t.
  Coercion SLprop.sl_pred : SLprop.t >-> Funclass.
End SLNotations.
