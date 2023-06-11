From SLFun Require Import Util Values.
From Coq   Require Import Setoids.Setoid.


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

Module SLprop.

  Record t := mk_sl_pred {
    sl_pred :> FMem.t -> Prop;
    sl_wf   : forall m0 m1 (MEQ : FMem.eq m0 m1) (HM0 : sl_pred m0), sl_pred m1;
  }.

  Bind Scope slprop_scope with t.

  Definition eq (h0 h1 : t) : Prop :=
    forall m : FMem.t, h0 m <-> h1 m.

  Definition imp (h0 h1 : t) : Prop :=
    forall m, h0 m -> h1 m.

  Global Instance slprop_PartialOrder: Rel.MakePartialOrder eq imp.
  Proof.
    split.
    - intros ? ?; cbn.
      unfold Basics.flip, eq, imp.
      setoid_rewrite Rel.forall_and_comm.
      reflexivity.
    - Rel.by_expr (Rel.pull sl_pred (Rel.point FMem.t Basics.impl)).
  Qed.

  Lemma imp_morph:
    forall x y : t, eq x y -> forall x0 y0 : t, eq x0 y0 -> imp x x0 <-> imp y y0.
  Proof.
    exact (Morphisms.PartialOrder_proper (eqA := eq) (R := imp) _).
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

  Lemma eq_iff_imp h0 h1:
    eq h0 h1 <-> (imp h0 h1 /\ imp h1 h0).
  Proof.
    apply (Rel.partial_order_eq_iff eq imp).
  Qed.

  (* [impp] : implies pure *)

  Definition impp (h : SLprop.t) (P : Prop) :=
    forall m, h m -> P.

  Global Add Morphism impp
    with signature eq ==> iff ==> iff
    as impp_morph.
  Proof.
    intros h0 h1 Eh P0 p1 EP.
    unfold impp.
    setoid_rewrite Eh.
    setoid_rewrite EP.
    reflexivity.
  Qed.

  Lemma impp_drop [h : SLprop.t] [P : Prop]
    (C : P):
    impp h P.
  Proof.
    intros ? ?; exact C.
  Qed.

  Lemma impp_True (h : SLprop.t):
    impp h True.
  Proof.
    apply impp_drop; constructor.
  Qed.

  Lemma impp_cut [h : SLprop.t] [P Q : Prop]
    (C0 : impp h P)
    (C1 : P -> impp h Q):
    impp h Q.
  Proof.
    intros m H.
    exact (C1 (C0 m H) m H).
  Qed.

  Lemma impp_enough [h : SLprop.t] [P Q : Prop]
    (C0 : impp h P)
    (C1 : P -> Q):
    impp h Q.
  Proof.
    apply (impp_cut C0).
    intro H; apply impp_drop, C1, H.
  Qed.

  Lemma cut_pure [h0 h1 : SLprop.t] (P : Prop)
    (C0 : impp h0 P)
    (C1 : P -> SLprop.imp h0 h1):
    SLprop.imp h0 h1.
  Proof.
    intros m H0.
    apply (C1 (C0 m H0) m H0).
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

  Lemma star_comm12 h0 h1 h2:
    eq (h0 ** h1 ** h2) (h1 ** h0 ** h2).
  Proof.
    rewrite <- star_assoc.
    setoid_rewrite star_comm at 2.
    apply star_assoc.
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

  Lemma impp_star h0 h1 P0 P1
    (H0 : impp h0 P0)
    (H1 : impp h1 P1):
    impp (h0 ** h1) (P0 /\ P1).
  Proof.
    intros ? (m0 & m1 & _ & M0 & M1).
    split; [eapply H0|eapply H1]; eassumption.
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
  
  Lemma imp_pure_l1 (P : Prop) (h : t)
    (C : P -> imp emp h):
    imp (pure P) h.
  Proof.
    rewrite <- star_emp_r.
    apply imp_pure_l, C.
  Qed.

  Lemma imp_pure_r (P : Prop) (h0 h1 : SLprop.t)
    (HP : P)
    (C : imp h0 h1):
    imp h0 (pure P ** h1).
  Proof.
    intros m H0%C.
    apply star_pure; auto.
  Qed.

  Lemma imp_pure_r1 (P : Prop) (h : SLprop.t)
    (HP : P)
    (C : imp h emp):
    imp h (pure P).
  Proof.
    setoid_rewrite <- star_emp_r at 2.
    apply imp_pure_r; auto.
  Qed.

  Lemma impp_pure P:
    impp (pure P) P.
  Proof.
    intros m H; apply H.
  Qed.

  Lemma impp_pure_l [P : Prop] [h Q]
    (C : P -> impp h Q):
    impp (pure P ** h) Q.
  Proof.
    eapply impp_cut.
    - apply impp_star; [apply impp_pure|apply impp_True].
    - intros (H & _).
      eapply impp_enough.
      apply impp_star; [apply impp_True|apply (C H)].
      tauto.
  Qed.
  
  Lemma impp_pure_l1 [P Q : Prop]
    (C : P -> Q):
    impp (pure P) Q.
  Proof.
    eapply impp_enough, C.
    apply impp_pure.
  Qed.

  Lemma impp_eq [h P]
    (H : impp h P):
    eq h (pure P ** h).
  Proof.
    apply antisymmetry.
    - intros m M.
      apply star_pure.
      exact (conj (H m M) M).
    - apply imp_pure_l. reflexivity.
  Qed.


  (* [ex] : exists *)

  Program Definition ex (A : Type) (h : A -> t) : t :=
    mk_sl_pred (fun m => exists x : A, h x m) _.
  Next Obligation.
    setoid_rewrite <- MEQ; eauto.
  Qed.

  Global Add Parametric Morphism A : (ex A)
    with signature Morphisms.pointwise_relation A eq ==> eq
    as ex_morph.
  Proof.
    intros h0 h1 E m; simpl.
    setoid_rewrite E.
    reflexivity.
  Qed.

  Lemma exists_star A (h0 : A -> t) (h1 : t):
    eq (ex A h0 ** h1) (ex A (fun x => star (h0 x) h1)).
  Proof.
    intro m; split.
    - intros (m0 & m1 & J & (x & H0) & H1).
      exists x, m0, m1; eauto.
    - intros (x & (m0 & m1 & J & H0 & H1)).
      repeat (esplit; eauto).
  Qed.

  Lemma imp_exists A (h : A -> t) (wit : A):
    imp (h wit) (ex A h).
  Proof.
    exists wit; assumption.
  Qed.

  Lemma imp_exists_l A (h0 : A -> t) (h1 : t)
    (C : forall x : A, imp (h0 x) h1):
    imp (ex A h0) h1.
  Proof.
    intros m [x H0]; eapply C, H0.
  Qed.

  Lemma imp_exists_r A (h0 : t) (h1 : A -> t) (wit : A)
    (C : imp h0 (h1 wit)):
    imp h0 (ex A h1).
  Proof.
    rewrite <- imp_exists with (wit := wit); exact C.
  Qed.

  Lemma impp_exists_l [A h Q]
    (C : forall x : A, impp (h x) Q):
    impp (ex A h) Q.
  Proof.
    intros m [x M]; exact (C x m M).
  Qed.


  (* [wand] *)

  Program Definition wand (h0 h1 : t) : t :=
    mk_sl_pred (fun m0 => forall m m1 (J : FMem.is_join m m0 m1) (H0 : h0 m1), h1 m) _.
  Next Obligation.
    eapply HM0; eauto.
    rewrite MEQ; exact J.
  Qed.

  Lemma elim_wand (h0 h1 : t):
    imp (wand h0 h1 ** h0) h1.
  Proof.
    intros m (m0 & m1 & J & HW & H0).
    eapply HW; eauto.
  Qed.

  Lemma intro_wand (h0 h1 h2 : t)
    (H : imp (h0 ** h1) h2):
    imp h0 (wand h1 h2).
  Proof.
    intros m0 H0 m m1 J H1.
    eapply H; exists m0, m1; eauto.
  Qed.


  (* [cell] : points-to *)

  Program Definition cell (p : ptr) (d : memdata) : t :=
    mk_sl_pred (fun m => p <> NULL /\ FMem.eq m (FMem.cell p d)) _.
  Next Obligation.
    rewrite <- MEQ; auto.
  Qed.

  Lemma cell_non_null p v:
    impp (SLprop.cell p v) (p <> NULL).
  Proof.
    intro; cbn; tauto.
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
      | REx   (A : Type) (h : A -> reified)
      | RAtom (h : t).

    Fixpoint reflect (h : reified) : t :=
      match h with
      | REmp        => emp
      | RPure P     => pure P
      | RStar h0 h1 => reflect h0 ** reflect h1
      | REx   A h   => ex A (fun x => reflect (h x))
      | RAtom h     => h
      end.

    Inductive reifyI : reified -> t -> Prop :=
      | RIEmp    : reifyI REmp emp
      | RIPure P : reifyI (RPure P) (pure P)
      | RIPureTrue :
                   reifyI REmp (pure Logic.True)
      | RIStar r0 r1 h0 h1 (R0 : reifyI r0 h0) (R1 : reifyI r1 h1) :
                   reifyI (RStar r0 r1) (h0 ** h1)
      | RIEx   A r h (R : forall x : A, reifyI (r x) (h x)) :
                   reifyI (REx A r) (ex A h)
      | RIExUnit r h (R : reifyI r (h tt)):
                   reifyI r (ex unit h)
      | RIAtom h : reifyI (RAtom h) h.

    Lemma reifyI_reflect r h:
      reifyI r h -> eq (reflect r) h.
    Proof.
      induction 1; simpl; try reflexivity.
      - (* RIPureTrue *) intro; cbn; tauto.
      - (* RIStar     *) rewrite IHreifyI1, IHreifyI2; reflexivity.
      - (* RIEx       *) setoid_rewrite H; reflexivity.
      - (* RIExUnit   *)
        rewrite IHreifyI; intro; cbn.
        split; [exists tt | intros [[]]]; auto.
    Qed.

    (* solves a goal [reifyI ?R h] *)
    Ltac reify_core :=
      match goal with |- reifyI _ ?h =>
      match h with
      | emp             => apply RIEmp
      | pure Logic.True => apply RIPureTrue
      | pure ?P         => apply RIPure
      | star ?h0 ?h1    => apply RIStar; [reify_core h0 | reify_core h1]
      | ex   unit ?h    => apply RIExUnit; cbn beta iota delta; reify_core
      | ex   ?A ?h      => apply RIEx;
                           let x := fresh "x" in intro x; cbn beta; reify_core
      | ?h              => apply RIAtom
      end end.
    
    (* adds an hypothesis [reifyI r h] to the goal *)
    Ltac reify h :=
      let R := fresh "Reified" in
      eassert (reifyI _ h) as R;
      [ reify_core | revert R ].


    Definition r_rewrite_3:
      let Goal h0 h1 := {h : reified | eq (reflect h) (reflect h0 ** reflect h1)} in
      forall (r2 : forall (h0 h1 : reified), Goal h0 h1) h0 h1, Goal h0 h1.
    Proof.
      intros Goal r2 h0 h1.
      unshelve refine (
        let def : Goal h0 h1 := r2 h0 h1 in
        match h1 as h1' return Goal h0 h1' -> Goal h0 h1' with
        | RStar h1 h2 => fun _ =>
            let (rr2, e) := r2 h0 h1 in
            let def : Goal h0 (RStar h1 h2) := exist _ (RStar rr2 h2) _ in
            match rr2 as rr2' return
              eq (reflect rr2') (reflect h0 ** reflect h1) -> _
            with
            | RStar h0' h1' => fun e => exist _ (RStar h0' (RStar h1' h2)) _
            | _ => fun _ => def
            end e
        | _ => fun def => def
        end def);
      simpl.
      - rewrite e, star_assoc; reflexivity.
      - rewrite <- star_assoc, e, star_assoc; reflexivity.
    Defined.

    Local Lemma sl_eq_refl h: eq h h.
    Proof. reflexivity. Qed.

    Fixpoint r_rewrite_2 (h0 h1 : reified) {struct h1}:
      {h : reified | eq (reflect h) (reflect h0 ** reflect h1)}.
    Proof.
      pose (Goal h0 h1 := {h : reified | eq (reflect h0 ** reflect h1) (reflect h)}).
      cut (Goal h0 h1).
        intros [h E]; exists h; symmetry; exact E.
      refine (match h1 as h1' return Goal h0 h1' with
              | REmp     => exist _ h0 _
              | REx A h1 => exist _ (REx A (fun x => proj1_sig (r_rewrite_3 r_rewrite_2 h0 (h1 x)))) _
              | RPure Q  =>
                  match h0 as h0' return Goal h0' (RPure Q) with
                  | RPure P => exist _ (RPure (P /\ Q)) _
                  | h0      => exist _ (RStar (RPure Q) h0) (star_comm _ _)
                  end
              | h1       => exist _ (RStar h0 h1) (sl_eq_refl _)
              end);
      simpl; auto using star_emp_r, pure_star_pure.
      - rewrite star_comm, exists_star.
        apply ex_morph; intro x.
        case r_rewrite_3 as [rw E]; simpl.
        rewrite E, star_comm; reflexivity.
    Defined.

    Definition r_rewrite_star := r_rewrite_3 r_rewrite_2.

    Fixpoint r_rewrite_flat (h : reified) (acc : reified) {struct h} : reified :=
      match h with
      | REmp        => acc
      | RStar h0 h1 => r_rewrite_flat h0 (r_rewrite_flat h1 acc)
      | REx A h     => REx A (fun x => r_rewrite_flat (h x) acc)
      | h           => proj1_sig (r_rewrite_star h acc)
      end.

    Lemma r_rewrite_flat_correct h acc:
      eq (reflect (r_rewrite_flat h acc)) (reflect h ** reflect acc).
    Proof.
      revert acc; induction h; intro;
        try solve [apply (proj2_sig (r_rewrite_star _ acc))]; simpl.
      - rewrite star_emp_l; reflexivity.
      - rewrite IHh1, IHh2, star_assoc; reflexivity.
      - setoid_rewrite H; rewrite exists_star; reflexivity.
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
      reifyI r h ->
      eq h (reflect (r_normalize r)).
    Proof.
      intros <-%reifyI_reflect. rewrite r_normalize_correct. reflexivity.
    Qed.

    (* Solve a goal [h = ?h] *)
    Ltac normalize_core :=
      cbn;
      lazymatch goal with |- eq ?h _ =>
          let R := fresh "R" in
          reify h; intro R;
          apply normalize_r_eq in R; cbn in R;
          exact R
      end.

    Ltac normalize :=
      lazymatch goal with
      | |- eq ?h0 ?h1 =>
          first [
            is_evar h0; is_evar h1; reflexivity
          | is_evar h1; normalize_core
          | is_evar h0; symmetry; normalize_core
          | etransitivity; [normalize_core|etransitivity; [|symmetry;normalize_core]]]
      | |- sl_pred _ _ =>
          eapply sl_pred_eq; [normalize_core|]
      | |- imp _ _ =>
          eapply imp_morph; [normalize_core|normalize_core|]
      | |- _ = _ => reflexivity
      end.

  End Norm.

  Ltac split_impp :=
    try lazymatch goal with
    | |- impp (pure   _) _ => apply impp_pure
    | |- impp (star _ _) _ => apply impp_star; split_impp
    end.
End SLprop.

Import Util.Tac.

(* DB for [normalize].
   should solves goal [Arrow ?goal1 goal0] *)
Global Create HintDb NormalizeDB discriminated.
Global Hint Constants Opaque : NormalizeDB.
Global Hint Variables Opaque : NormalizeDB.
Ltac normalize :=
  refine (cut_Arrow _ _);
  [ solve_db NormalizeDB | try exact Logic.I].

Global Hint Extern 1 (Arrow _ (SLprop.eq ?h0 ?h1)) =>
  mk_Arrow_tac ltac:(fun _ => first
  [ is_evar h0; is_evar h1; reflexivity
  | is_evar h1; SLprop.Norm.normalize_core
  | is_evar h0; symmetry; SLprop.Norm.normalize_core
  | etransitivity; [SLprop.Norm.normalize_core | etransitivity; [|symmetry;SLprop.Norm.normalize_core]]
  ]) : NormalizeDB.

Global Hint Extern 1 (Arrow _ (SLprop.sl_pred _ _)) =>
  mk_Arrow_tac ltac:(fun _ =>
  eapply SLprop.sl_pred_eq; [SLprop.Norm.normalize_core|])
    : NormalizeDB.

Global Hint Extern 1 (Arrow _ (SLprop.imp _ _)) =>
  mk_Arrow_tac ltac:(fun _ =>
  eapply SLprop.imp_morph; [SLprop.Norm.normalize_core|SLprop.Norm.normalize_core|])
    : NormalizeDB.

Global Hint Extern 1 (Arrow _ (SLprop.impp _ _)) =>
  mk_Arrow_tac ltac:(fun _ =>
  eapply SLprop.impp_morph; [SLprop.Norm.normalize_core|reflexivity|])
    : NormalizeDB.

Global Hint Extern 1 (Arrow _ (_ = _)) =>
  mk_Arrow_tac ltac:(fun _ => reflexivity) : NormalizeDB.

Module Tactics.
  #[export] Hint Extern 1 (Arrow _ (SLprop.imp (SLprop.star (SLprop.pure _) _) _)) =>
     exact (mk_Arrow (SLprop.imp_pure_l _ _ _)) : IntroDB.
  
  #[export] Hint Extern 1 (Arrow _ (SLprop.imp (SLprop.pure _) _)) =>
     exact (mk_Arrow (SLprop.imp_pure_l1 _ _)) : IntroDB.

  #[export] Hint Extern 1 (Arrow _ (SLprop.imp (SLprop.ex _ _) _)) =>
     exact (mk_Arrow (SLprop.imp_exists_l _ _ _)) : IntroDB.
  
  Local Lemma Apply_imp_pure (P : Prop) h0 h1:
    Arrow ({_ : P & SLprop.imp h0 h1}) (SLprop.imp h0 (SLprop.star (SLprop.pure P) h1)).
  Proof.
    constructor; intros [H0 H1].
    apply SLprop.imp_pure_r; assumption.
  Qed.
  
  Local Lemma Apply_imp_pure1 (P : Prop) h:
    Arrow ({_ : P & SLprop.imp h SLprop.emp}) (SLprop.imp h (SLprop.pure P)).
  Proof.
    constructor; intros [H0 H1].
    apply SLprop.imp_pure_r1; assumption.
  Qed.

  Local Lemma Apply_imp_exists A h0 h1:
    Arrow ({x : A & SLprop.imp h0 (h1 x)}) (SLprop.imp h0 (SLprop.ex A h1)).
  Proof.
    constructor; intros [x H].
    apply SLprop.imp_exists_r with (wit := x); assumption.
  Qed.
  
  #[export] Hint Extern 1 (Arrow _ (SLprop.imp _ (SLprop.star (SLprop.pure _) _))) =>
     exact (Apply_imp_pure _ _ _) : ApplyDB.

  #[export] Hint Extern 1 (Arrow _ (SLprop.imp _ (SLprop.pure _))) =>
     exact (Apply_imp_pure1 _ _) : ApplyDB.

  #[export] Hint Extern 1 (Arrow _ (SLprop.imp _ (SLprop.ex _ _))) =>
     exact (Apply_imp_exists _ _ _) : ApplyDB.


  #[export] Hint Extern 1 (Arrow _ (SLprop.impp (SLprop.star (SLprop.pure _) _) _)) =>
     exact (mk_Arrow (@SLprop.impp_pure_l _ _ _)) : IntroDB.
  
  #[export] Hint Extern 1 (Arrow _ (SLprop.impp (SLprop.pure _) _)) =>
     exact (mk_Arrow (@SLprop.impp_pure_l1 _ _)) : IntroDB.

  #[export] Hint Extern 1 (Arrow _ (SLprop.impp (SLprop.ex _ _) _)) =>
     exact (mk_Arrow (@SLprop.impp_exists_l _ _ _)) : IntroDB.
End Tactics.

Module SLNotations.
  Include SLprop.Notations.
  Bind Scope slprop_scope with SLprop.t.
  Coercion SLprop.sl_pred : SLprop.t >-> Funclass.
End SLNotations.

Section Test.
  Import SLprop SLNotations.

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

  Local Lemma test_normalize_2 h0 A h1:
    eq (h0 ** ex A h1 ** emp) (ex A (fun x => emp ** h0 ** h1 x))%slprop.
  Proof.
    normalize. reflexivity.
  Qed.

  Local Lemma test_normalize_3 A h P h1:
    eq (h ** ex A (fun x => pure (P x) ** h1 x))%slprop
       (ex A (fun x => (pure (P x) ** h ** h1 x)))%slprop.
  Proof.
    etransitivity. normalize. reflexivity.
  Qed.
  
  Local Lemma test_normalize_4 A B h0 h1 P Q:
    eq (h0 ** ex A (fun x => ex B (h1 x) ** pure (P x)) ** pure Q)%slprop
       (ex A (fun x => ex B (fun y => (pure (P x /\ Q) ** h0 ** h1 x y))))%slprop.
  Proof.
    etransitivity. normalize. reflexivity.
  Qed.

  Local Lemma test_normalize_5 P:
    impp (emp ** pure P) P.
  Proof.
    normalize. apply impp_pure.
  Qed.
End Test.
