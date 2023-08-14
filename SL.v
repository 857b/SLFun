From SLFun Require Import Util Values.
From Coq   Require Import Setoids.Setoid.

Declare Scope slprop_scope.
Delimit Scope slprop_scope with slprop.


(* [FMem] *)

Module FCell.

  Definition t := option memdata.

  Definition emp : t := None.


  Inductive is_join : forall (c0 c1 c : t), Prop :=
    | J_Left  c : is_join c emp c
    | J_Right c : is_join emp c c.

  Lemma is_join_unique [c0 c1]:
    unique eq (is_join c0 c1).
  Proof.
    do 2 inversion 1; reflexivity.
  Qed.

  Lemma is_join_comm c0 c1 c:
    is_join c0 c1 c <-> is_join c1 c0 c.
  Proof.
    split; destruct 1; constructor.
  Qed.

  Lemma is_join_assoc [c0 c1 c2 c01 c012]:
    is_join c0  c1 c01  ->
    is_join c01 c2 c012 ->
    exists c12,
      is_join c1 c2  c12 /\
      is_join c0 c12 c012.
  Proof.
    do 2 destruct 1; do 3 econstructor.
  Qed.

  Lemma is_join_emp_l c c':
    is_join emp c c' <-> c = c'.
  Proof.
    split; inversion 1; constructor.
  Qed.

  Lemma is_join_emp_r c c':
    is_join c emp c' <-> c = c'.
  Proof.
    split; inversion 1; constructor.
  Qed.


  Inductive is_join_set [A : Type] (e : relation A) (cs : A -> t -> Prop) : t -> Prop :=
    | JS_None
        (N : forall x : A, cs x emp):
        is_join_set e cs emp
    | JS_Some
        (x : A) (v : memdata)
        (V : cs x (Some v))
        (N : forall x' : A, e x x' \/ cs x' None):
        is_join_set e cs (Some v).

  Lemma is_join_set_unique [A] [e : relation A] [cs]
    (U : forall x, unique eq (cs x))
    (M : forall x x', e x x' -> forall c, cs x c <-> cs x' c):
    unique eq (@is_join_set A e cs).
  Proof.
    do 2 inversion_clear 1; try reflexivity.
    1,2:eapply U; eauto.
    - case (N0 x0) as [E|C].
      2:{ exfalso; cut (None = Some v). discriminate 1.
          eapply U; eassumption. }
      eapply (M _ _ E) in V.
      eapply U; eassumption.
  Qed.

  Lemma is_join_set_F [A B] (F : A -> B -> Prop) (eA : relation A) (eB : relation B)
    (csA : A -> t -> Prop) (csB : B -> t -> Prop) c
    (HM : forall (x x' : A) (y y' : B), eA x x' -> F x y -> F x' y' -> eB y y')
    (HF : forall (x : A) v, csA x (Some v) -> exists y : B, F x y /\ csB y (Some v))
    (HB : forall y : B, csB y None \/ exists x : A, F x y /\ forall c, csA x c -> csB y c):
    @is_join_set A eA csA c ->
    @is_join_set B eB csB c.
  Proof.
    intros [|].
    - apply JS_None.
      intro y.
      case (HB y) as [Ny|(x & _ & Ex)].
      + apply Ny.
      + apply Ex, N.
    - case (HF x _ V) as (y & Fx & Ex).
      apply JS_Some with (x := y).
      + apply Ex.
+ intro y'.
        case (HB y') as [Ny|(x' & Fx' & Ex')]; auto.
        case (N  x') as [|]; [left | right].
        * eapply HM; eauto.
        * apply Ex'; assumption.
  Qed.

  Global Add Parametric Morphism [A]: (@is_join_set A)
    with signature
      relation_equivalence ==>
      (Morphisms.pointwise_relation A (Morphisms.pointwise_relation t iff)) ==>
      Logic.eq ==> iff
    as is_join_set_morph.
  Proof.
    intros e0 e1 E0 cs0 cs1 E1 c.
    eenough _ as pf.
      { split; [revert e0 e1 E0 cs0 cs1 E1; exact pf|apply pf; symmetry; auto]. }
    clear; do 6 intro.
    apply is_join_set_F with (F := Logic.eq).
    1:setoid_rewrite (fun x y => E0 x y); congruence.
    1,2:setoid_rewrite E1; eauto.
  Qed.
  Global Arguments is_join_set_morph [A e0 e1] Ee [cs0 cs1] Ecs [c c'] Ec : rename.

  Definition is_join_subset [A] (P : A -> Prop) (e : relation A) (cs : A -> t -> Prop) : t -> Prop :=
    @is_join_set (sig P) (fun x0 x1 => e (proj1_sig x0) (proj1_sig x1)) (fun x0 => cs (proj1_sig x0)).

  Lemma is_join_set_subset [A] (P : A -> Prop) (e : relation A) (cs : A -> t -> Prop) (c : t)
    (P_EM : forall x, P x \/ ~P x)
    (P_MH : forall x x', e x x' -> P x' -> P x):
    @is_join_set A e cs c ->
    exists c', is_join_subset P e cs c'.
  Proof.
    intros [|].
    - exists None; apply JS_None.
      intros []; apply N.
    - case (P_EM x) as [Px|nPx].
      + exists (Some v); apply JS_Some with (x := exist _ x Px).
        * exact V.
        * intros [x']; cbn.
          case (N x'); auto.
      + exists None; apply JS_None.
        intros [x']; cbn.
        case (N x') as [Ex|]; auto.
        exfalso; eapply nPx, P_MH; eauto.
  Qed.

  Section Join_Set_Group.
    Context [A B] (G : B -> A -> Prop) (eA : relation A) (eB : relation B) (cs : A -> t -> Prop) (c : t)
      {eA_eqv : Equivalence eA}
      {eB_eqv : Equivalence eB}
      (PART   : forall x : A, ex1 eB (fun y => G y x))
      (eB_EM  : forall y0 y1, eB y0 y1 \/ ~eB y0 y1)
      (HmG    : forall y0 y1 (Ey : eB y0 y1) x0 x1 (Ex : eA x0 x1), G y0 x0 -> G y1 x1).

    Lemma is_join_set_group:
      @is_join_set A eA cs c ->
      @is_join_set B eB (fun y => @is_join_subset A (G y) eA cs) c.
    Proof.
      destruct 1.
      - apply JS_None.
        intro; apply JS_None.
        intros []; apply N.
      - case (PART x) as (y & Gy & Uy).
        apply JS_Some with (x := y).
        + eapply JS_Some with (x := exist _ x Gy).
          * exact V.
          * intros []; cbn.
            apply N.
        + intro y'.
          case (eB_EM y y') as [|neB]; auto.
          right.
          apply JS_None.
          intros [x' Gx']; cbn.
          case (N x') as [HeA|]; auto.
          exfalso; apply neB.
          eapply Uy, HmG, Gx';
            try reflexivity; symmetry; auto.
    Qed.

    Lemma is_join_set_ungroup:
      @is_join_set B eB (fun y => @is_join_subset A (G y) eA cs) c ->
      @is_join_set A eA cs c.
    Proof.
      destruct 1 as [|y].
      - apply JS_None.
        intro x.
        case (PART x) as (y & Gy & _).
        specialize (N y); inversion_clear N.
        refine (N0 (exist _ x Gy)).
      - inversion_clear V as [|[x Gx] _v V0 N0];
          cbn in V0, N0.
        apply JS_Some with (x := x).
        { exact V0. }
        intro x'.
        case (PART x') as (y' & Gy' & _).
        case (N y') as [Ey|JN].
        + refine (N0 (exist _ x' _)).
          eapply HmG, Gy';
            try reflexivity; symmetry; auto.
        + right.
          inversion_clear JN.
          refine (N1 (exist _ x' Gy')).
    Qed.
  End Join_Set_Group.

  Lemma is_join_set_2 c0 c1 c:
    @is_join_set bool Logic.eq (fun b c => c = if b then c0 else c1) c <-> is_join c0 c1 c.
  Proof.
    split.
    - destruct 1.
      + rewrite <-(N true), <-(N false).
        constructor.
      + case (N (negb x)) as [C|N'].
          { exfalso; revert C; case x; discriminate 1. }
          destruct x; cbn in *; rewrite <- V, <- N'; constructor.
    - destruct 1, c.
      1,3:unshelve eapply JS_Some;
          [ constructor | reflexivity
          | intros []; constructor; reflexivity ].
      1,2:apply JS_None; intros []; reflexivity.
  Qed.
End FCell.

Module UPred.
  Record t (A : Type) (e : relation A) := mk {
    p   :> A -> Prop;
    unq : ex1 e p;
  }.
  Global Arguments mk  [A e] [p].
  Global Arguments p   [A e].
  Global Arguments unq [A e].

  Definition mk_s [A : Type] [e : relation A] [P : A -> Prop] (E : ex1 e P):
    t (sig P) (fun x0 x1 => e (proj1_sig x0) (proj1_sig x1)).
  Proof.
    exists (fun x => True).
    case E as (x & Ex & Ux).
    exists (exist _ x Ex); split; auto.
    intros [x'] _.
    apply Ux; auto.
  Qed.

  Definition eq {A e} (p0 p1 : t A e) : Prop :=
    forall x : A, p0 x <-> p1 x.

  Global Instance eq_Equivalence {A e} : Equivalence (@eq A e).
  Proof.
    Rel.by_expr (Rel.pull (@p A e) (Rel.point A iff)).
  Qed.


  Definition bind [A : Type] [e : relation A] (p : t A e) (P : A -> Prop) :=
    forall x : A, p x -> P x.
  Global Arguments bind _ _ !p _/.

  Global Add Parametric Morphism A e : (@bind A e)
    with signature (@eq A e) ==> Morphisms.pointwise_relation A iff ==> iff
    as bind_morph.
  Proof.
    intros p0 p1 Ep P0 P1 EP.
    apply Morphisms_Prop.all_iff_morphism; intro x.
    rewrite (Ep x), (EP x).
    reflexivity.
  Qed.

  Lemma bind_comm [A0 A1 : Type] (p0 : t A0 Logic.eq) (p1 : t A1 Logic.eq) (P : A0 -> A1 -> Prop):
    bind p0 (fun x0 => bind p1 (fun x1 => P x0 x1)) <->
    bind p1 (fun x1 => bind p0 (fun x0 => P x0 x1)).
  Proof.
    split;
    intros H ? ? ? ?; apply H; assumption.
  Qed.

  Lemma eq_morph {A : Type} {P : A -> Prop}:
    forall x x', x = x' -> P x -> P x'.
  Proof.
    intros ? ? ->; auto.
  Qed.

  Lemma Get_bind_u [A e] (p : t A e) [x] (Hx : p x) (Ux : forall x', p x' -> e x x'):
    forall (P : A -> Prop), (forall x', e x x' -> P x -> P x') -> bind p P <-> P x.
  Proof.
    intros P M; split.
    - intros H; apply H, Hx.
    - intros HP x' Hp'.
      eapply M, HP.
      apply Ux, Hp'.
  Qed.

  Lemma Get_bind_x [A e] {eqv : Equivalence e} (p : t A e) [x] (Hx : p x):
    forall (P : A -> Prop), (forall x', e x x' -> P x -> P x') -> bind p P <-> P x.
  Proof.
    case (unq p) as (x' & Hx' & U).
    setoid_rewrite (U x Hx) in U; clear x' Hx'.
    apply Get_bind_u; auto.
  Qed.

  Lemma Get_bind_e [A e] (p : t A e):
    exists x : A, forall (P : A -> Prop), (forall x', e x x' -> P x -> P x') -> bind p P <-> P x.
  Proof.
    case (unq p) as (x & Ex & Ux).
    exists x.
    apply Get_bind_u; auto.
  Qed.

  Lemma Get_bind [A] (p : t A Logic.eq):
    exists x : A, forall (P : A -> Prop), bind p P <-> P x.
  Proof.
    case (Get_bind_e p) as [x H].
    exists x.
    intro; apply H, eq_morph.
  Qed.

  Ltac Get p x :=
    let E := fresh "E" in
    case (Get_bind p) as [x E];
    repeat setoid_rewrite E;
    clear E.

  Ltac auto_Get :=
    lazymatch goal with
    | |- context[bind ?p _] =>
        let x := fresh "x" in
        Get p x
    end.

  Lemma p_iff_bind [A : Type] (p : t A Logic.eq) (x : A):
    p x <-> bind p (fun x' => x' = x).
  Proof.
    unfold bind.
    case (ex1_elim_iff eq_morph (unq p)) as [x0 E].
    setoid_rewrite E.
    intuition subst; auto.
  Qed.

  Lemma eq_iff_bind {A : Type} {p0 p1 : t A Logic.eq}:
    eq p0 p1 <-> bind p0 (fun x0 => bind p1 (fun x1 => x0 = x1)).
  Proof.
    unfold eq.
    setoid_rewrite p_iff_bind.
    do 2 auto_Get.
    intuition subst; eauto.
    symmetry; apply H; reflexivity.
  Qed.


  Program Definition one [A : Type] {e : relation A} {refl : Reflexive e} (x : A) : t A e :=
    {| p := e x |}.
  Next Obligation.
    exists x; intuition.
  Qed.

  Lemma bind_one [A] (x : A) {P : A -> Prop}:
    bind (one x) P <-> P x.
  Proof.
    cbn; intuition subst; auto.
  Qed.

  Global Arguments one : simpl never.


  Notation "' x := f 'in' g" := (bind f (fun x => g))
    (at level 200, x pattern at level 0, right associativity).
End UPred.

Module FMem.
  Import UPred.
  
  Definition t := ptr -> UPred.t FCell.t Logic.eq.

  Definition eq : relation t :=
    Morphisms.pointwise_relation ptr UPred.eq.


  Definition mem_match (f : t) (m : mem) :=
    forall p v, f p (Some v) -> m p = v.

  Definition of_mem (m : mem) : t :=
    fun p => UPred.one (Some (m p)).

  Lemma match_of_mem m:
    mem_match (of_mem m) m.
  Proof.
    injection 1 as ->; reflexivity.
  Qed.


  Lemma make (P : ptr -> FCell.t -> Prop)
    (H : forall p, ex1 Logic.eq (P p)):
    {m : t | forall p, 'c := m p in P p c}.
  Proof.
    exists (fun p => UPred.mk (H p)).
    cbn; auto.
  Qed.

  Lemma of_pred (P : UPred.t t FMem.eq)
    (M : forall m m', FMem.eq m m' -> P m -> P m'):
    {m : t | P m}.
  Proof.
    case (make (fun p c' => 'm := P in 'c := m p in c' = c)) as [m Pm]. {
      intro p.
      case (UPred.Get_bind_e P) as [m Bm].
      setoid_rewrite Bm. 2:{
        intros m' Em.
        rewrite (Em p); auto.
      }
      UPred.Get (m p) c.
      exists c; eauto.
    }
    exists m.
    case (unq P) as (m' & Pm' & Um).
    eapply M, Pm'.
    intro p.
    apply UPred.eq_iff_bind; generalize (Pm p).
    UPred.Get (m p) c.
    intros Pmp c' Mc'.
    symmetry; apply (Pmp m'); eauto.
  Qed.


  Definition emp : t := fun _ => one FCell.emp.

  Definition is_join (m0 m1 m : t) : Prop :=
    forall p : ptr,
    'c0 := m0 p in 'c1 := m1 p in 'c := m p in
    FCell.is_join c0 c1 c.

  Global Add Morphism is_join
    with signature eq ==> eq ==> eq ==> iff
    as is_join_morph.
  Proof.
    intros ? ? E ? ? E0 ? ? E1.
    apply Morphisms_Prop.all_iff_morphism; intro p.
    setoid_rewrite (E  p).
    setoid_rewrite (E0 p).
    setoid_rewrite (E1 p).
    reflexivity.
  Qed.

  Lemma is_join_unique [m0 m1]:
    unique eq (is_join m0 m1).
  Proof.
    intros m m' J J' p; apply UPred.eq_iff_bind.
    generalize (J p), (J' p).
    repeat auto_Get.
    apply FCell.is_join_unique.
  Qed.

  Lemma is_join_comm m0 m1 m:
    is_join m0 m1 m <-> is_join m1 m0 m.
  Proof.
    unfold is_join.
    setoid_rewrite bind_comm at 1.
    setoid_rewrite FCell.is_join_comm at 1.
    reflexivity.
  Qed.

  Lemma is_join_assoc [m0 m1 m2 m01 m012]
    (J0 : is_join m0  m1 m01)
    (J1 : is_join m01 m2 m012):
    exists m12,
      is_join m1 m2 m12 /\
      is_join m0 m12 m012.
  Proof.
    case (make (fun p c =>
        'c0 := m0 p in 'c1 := m1 p in 'c2 := m2 p in 'c012 := m012 p in
        FCell.is_join c1 c2 c /\ FCell.is_join c0 c c012))
        as [m12 M]. {
      intro p.
      generalize (J0 p), (J1 p).
      do 5 auto_Get.
      intros J0' J1'.
      case (FCell.is_join_assoc J0' J1') as (c12 & J2 & J3).
      exists c12; intuition.
      eapply FCell.is_join_unique; eassumption.
    }
    exists m12.
    split; intro p; generalize (M p); do 5 auto_Get; tauto.
  Qed.

  Lemma is_join_emp_l m0 m:
    is_join emp m0 m <-> eq m m0.
  Proof.
    unfold is_join, emp.
    setoid_rewrite bind_one.
    setoid_rewrite FCell.is_join_emp_l.
    apply Morphisms_Prop.all_iff_morphism; intro.
    setoid_rewrite UPred.eq_iff_bind.
    repeat auto_Get.
    split; congruence.
  Qed.

  Lemma is_join_emp_r m0 m:
    is_join m0 emp m <-> eq m m0.
  Proof.
    rewrite is_join_comm.
    apply is_join_emp_l.
  Qed.


  Definition cell (p : ptr) (d : memdata) : t :=
    fun r => if Mem.ptr_eq r p then UPred.one (Some d) else UPred.one (FCell.emp).


  Definition is_join_set [A : Type] (e : relation A) (ms : A -> t) (m : t) : Prop :=
    forall r, 'c := m r in FCell.is_join_set e (fun x => ms x r) c.

  Lemma is_join_set_unique [A] [e : relation A] [ms]
    (M : forall x x', e x x' -> eq (ms x) (ms x')):
    unique eq (@is_join_set A e ms).
  Proof.
    intros m m' J J' p.
    apply UPred.eq_iff_bind; generalize (J p) (J' p).
    do 2 UPred.auto_Get.
    apply FCell.is_join_set_unique; clear x x0.
    - intro x.
      apply ex1_unique, (ms x p); auto_tc.
      apply UPred.eq_morph.
    - intros x0 x1 E c.
      apply M, E.
  Qed.

  Lemma is_join_set_F [A B] (F : A -> B -> Prop) (eA : relation A) (eB : relation B)
    (msA : A -> t) (msB : B -> t) m
    (HM : forall (x x' : A) (y y' : B), eA x x' -> F x y -> F x' y' -> eB y y')
    (HF : forall x : A, eq (msA x) emp \/ exists y : B, F x y /\ eq (msA x) (msB y))
    (HB : forall y : B, eq (msB y) emp \/ exists x : A, F x y /\ eq (msA x) (msB y))
    (J : @is_join_set A eA msA m):
    @is_join_set B eB msB m.
  Proof.
    intro p; generalize (J p).
    UPred.Get (m p) c.
    apply (FCell.is_join_set_F F).
    - exact HM.
    - intros x v Mx.
      case (HF x) as [Ex|(y & Fx & Ex)].
      + exfalso; apply Ex in Mx; discriminate Mx.
      + exists y; intuition.
        apply Ex; auto.
    - intro y.
      case (HB y) as [Ex|(x & Fx & Ex)]; [left|right].
      + apply Ex; reflexivity.
      + exists x; intuition.
        apply Ex; auto.
  Qed.

  Global Add Parametric Morphism A : (@is_join_set A)
    with signature
      relation_equivalence ==>
      (Morphisms.pointwise_relation A eq) ==>
      eq ==> iff
    as is_join_set_morph.
  Proof.
    symmetric_iff.
    intros e0 e1 Ee ms0 ms1 Ems m0 m1 Em J.
    cut (is_join_set e0 ms0 m1).
    - apply is_join_set_F with (F := @Logic.eq A);
        intuition subst; eauto.
      apply Ee; auto.
    - intro p.
      rewrite <- Em.
      apply (J p).
  Qed.
  Global Arguments is_join_set_morph [A e0 e1] Ee [ms0 ms1] Ems [m0 m1] Em : rename.

  Section Join_Set_Group.
    Context [A B] (G : B -> A -> Prop) (eA : relation A) (eB : relation B) (ms : A -> t) (m : t)
      {eA_eqv : Equivalence eA}
      {eB_eqv : Equivalence eB}
      (PART   : forall x : A, ex1 eB (fun y => G y x))
      (eB_EM  : forall y0 y1, eB y0 y1 \/ ~eB y0 y1)
      (G_EM   : forall x y, G y x \/ ~G y x)
      (HmG    : forall y0 y1 (Ey : eB y0 y1) x0 x1 (Ex : eA x0 x1), G y0 x0 -> G y1 x1)
      (Me     : forall x0 x1, eA x0 x1 -> FMem.eq (ms x0) (ms x1)).

    Let eG y : relation (sig (G y)) := fun x0 x1 => eA (proj1_sig x0) (proj1_sig x1).
    Let P y p := @FCell.is_join_set (sig (G y)) (eG y) (fun x => ms (proj1_sig x) p).

    Local Lemma P_unq x p: unique Logic.eq (P x p).
    Proof.
      apply FCell.is_join_set_unique.
      - intros [].
        refine (ex1_unique UPred.eq_morph (UPred.unq (ms _ p))).
      - intros [] []; unfold eG; cbn.
        refine (fun E => Me _ _ E p).
    Qed.

    Local Lemma P_ex_iff x p c c'
      (E : P x p c):
      P x p c' <-> c = c'.
    Proof.
      split.
      * apply P_unq, E.
      * intros <-; apply E.
    Qed.

    Lemma is_join_set_group
      (J : @is_join_set A eA ms m):
      exists msG : B -> t,
        @is_join_set B eB msG m /\
        forall y : B,
        @is_join_set (sig (G y)) (eG y) (fun x => ms (proj1_sig x)) (msG y).
    Proof.
      unshelve epose proof (msG_pf := fun y => make (P y) _). {
        intro p; apply ex1_intro2.
        + unfold P. generalize (J p); auto_Get.
          apply FCell.is_join_set_subset; auto.
          do 3 intro; apply HmG; try reflexivity; symmetry; auto.
        + apply P_unq.
      }
      exists (fun x => proj1_sig (msG_pf x)).
      split.
      - intro p; generalize (J p); UPred.Get (m p) c.
        intro Jp.
        apply FCell.is_join_set_group with (G := G) (eB := eB) in Jp; auto.
        eapply FCell.is_join_set_morph, Jp; try reflexivity.
        + intros x c'; rewrite (UPred.p_iff_bind (proj1_sig (msG_pf x) p)).
          specialize ((proj2_sig (msG_pf x)) p).
          UPred.auto_Get; intro Jx.
          symmetry; apply P_ex_iff, Jx.
      - intros x p.
        specialize ((proj2_sig (msG_pf x)) p).
        UPred.auto_Get; auto.
    Qed.

    Lemma is_join_set_ungroup (msG : B -> t)
      (J  : @is_join_set B eB msG m)
      (Js : forall y : B, @is_join_set (sig (G y)) (eG y) (fun x => ms (proj1_sig x)) (msG y)):
      @is_join_set A eA ms m.
    Proof.
      intro p.
      generalize (J p); UPred.Get (m p) c; intro Jp.
      apply FCell.is_join_set_ungroup with (G := G) (eB := eB); auto.
      eapply FCell.is_join_set_morph, Jp; try reflexivity.
      intros x c0.
      cbn; rewrite (UPred.p_iff_bind (msG x p)).
      generalize (Js x p); UPred.Get (msG x p) c'.
      apply P_ex_iff.
    Qed.
  End Join_Set_Group.

  Lemma is_join_set_2 m0 m1 m:
    @is_join_set bool Logic.eq (fun b => if b then m0 else m1) m <-> is_join m0 m1 m.
  Proof.
    apply Morphisms_Prop.all_iff_morphism; intro p.
    UPred.Get (m p) c.
    rewrite FCell.is_join_set_morph
      with (cs1 := fun (b : bool) c => 'c0 := m0 p in 'c1 := m1 p in c = if b then c0 else c1);
      try reflexivity.
    - do 2 UPred.auto_Get.
      apply FCell.is_join_set_2.
    - intros [] c';
      [ rewrite (UPred.p_iff_bind (m0 p)) | rewrite (UPred.p_iff_bind (m1 p)) ];
      do 2 UPred.auto_Get; intuition.
  Qed.
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

  Lemma eq_imp:
    subrelation eq imp.
  Proof.
    do 2 intro; apply eq_iff_imp.
  Qed.


  Definition mem_match (sl : SLprop.t) (m : mem) :=
    exists fm : FMem.t, FMem.mem_match fm m /\ sl fm.

  Lemma mem_match_morph_imp (sl0 sl1 : SLprop.t) (slE : SLprop.imp sl0 sl1) (m : mem):
    mem_match sl0 m -> mem_match sl1 m.
  Proof.
    intros (fm & ? & ?); exists fm; auto.
  Qed.

  Global Add Morphism mem_match
    with signature SLprop.eq ==> Logic.eq ==> iff
    as mem_match_sl_morph.
  Proof.
    symmetric_iff; intros ? ? slE.
    apply mem_match_morph_imp.
    rewrite slE; reflexivity.
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
    mk_sl_pred (fun m => exists m0 m1, FMem.is_join m0 m1 m /\ h0 m0 /\ h1 m1) _.
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
  
  Global Arguments SLprop.pure : simpl never.


  (* [ex] : exists *)

  Program Definition ex (A : Type) (h : A -> t) : t :=
    mk_sl_pred (fun m => exists x : A, h x m) _.
  Next Obligation.
    setoid_rewrite <- MEQ; eauto.
  Qed.

  Lemma ex_morph_imp [A P0 P1]
    (E : forall x : A, imp (P0 x) (P1 x)):
    imp (ex A P0) (ex A P1).
  Proof.
    intros h [x H0].
    exists x.
    apply E, H0.
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

  Global Arguments SLprop.ex : simpl never.


  (* [wand] *)

  Program Definition wand (h0 h1 : t) : t :=
    mk_sl_pred (fun m0 => forall m m1 (J : FMem.is_join m0 m1 m) (H0 : h0 m1), h1 m) _.
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


  (* [all] *)

  Program Definition all [A : Type] (e : relation A) (hs : A -> t) : t :=
    mk_sl_pred (fun m => exists ms : A -> FMem.t,
      (forall x x', e x x' -> FMem.eq (ms x) (ms x')) /\
      FMem.is_join_set e ms m /\
      forall x : A, hs x (ms x)) _.
  Next Obligation.
    setoid_rewrite <- MEQ; eauto.
  Qed.

  Lemma all_morph_imp [A e hs0 hs1]
    (E : forall x : A, imp (hs0 x) (hs1 x)):
    imp (all e hs0) (all e hs1).
  Proof.
    intro m; cbn.
    intros (ms & M & J & Hs0).
    exists ms; intuition.
    apply E, Hs0.
  Qed.

  Global Add Parametric Morphism A e : (@all A e)
    with signature (Morphisms.pointwise_relation A SLprop.eq) ==> SLprop.eq
    as all_morph_eq.
  Proof.
    intros hs0 hs1 E.
    apply eq_iff_imp; split;
    apply all_morph_imp; setoid_rewrite E; reflexivity.
  Qed.

  Lemma all_F_imp [A B] (F : A -> B -> Prop) (eA : relation A) (eB : relation B)
    (hsA : A -> t) (hsB : B -> t)
    {eB_refl : Reflexive eB}
    (HmF : forall (x x' : A) (y y' : B), F x y -> F x' y' -> eA x x' <-> eB y y')
    (HmB : forall (y y' : B), eB y y' -> SLprop.eq (hsB y) (hsB y'))
    (HF  : forall x : A, SLprop.eq (hsA x) emp \/ exists y : B, F x y /\ SLprop.imp (hsA x) (hsB y))
    (HB  : forall y : B, SLprop.eq (hsB y) emp \/ exists x : A, F x y /\ SLprop.imp (hsA x) (hsB y)):
    imp (all eA hsA) (all eB hsB).
  Proof.
    intro m; cbn.
    intros (msA & MA & JA & HsA).
    pose (P y m :=
      (SLprop.eq (hsB y) emp /\ FMem.eq m FMem.emp) \/
      (exists x : A, F x y /\ FMem.eq (msA x) m /\ SLprop.imp (hsA x) (hsB y))).
    assert (P_unique : forall y0 y1 m0 m1, eB y0 y1 -> P y0 m0 -> P y1 m1 -> FMem.eq m0 m1). {
      intros y0 y1 m0 m1 Ey M0 M1.
      case M0 as [(Hemp  & ->) | (x  & Fx  & <- & Hx)],
           M1 as [(Hemp' & ->) | (x' & Fx' & <- & Hx')].
      * reflexivity.
      * symmetry.
        apply HmB in Ey.
        rewrite <- Ey, Hemp in Hx'.
        apply (Hx' _ (HsA x')).
      * apply HmB in Ey.
        rewrite Ey, Hemp' in Hx.
        apply (Hx _ (HsA x)).
      * eapply MA, HmF; eassumption.
    }
    enough (exists msB : B -> FMem.t, forall y, P y (msB y)) as [msB MB].
    - clear HB; exists msB.
      splits.
      + intros y y' Ey.
        apply (P_unique y y'); auto.
      + eapply (FMem.is_join_set_F F), JA.
        * intros; eapply HmF; eassumption.
        * intro x.
          case (HF x) as [Ex | (y & Fx & IMP)]; [left|right].
          -- apply Ex, HsA.
          -- exists y; split; auto.
             case (MB y) as [(Hemp & ->) | (x' & Fx' & <- & _)].
             ++ specialize (HsA x);
                apply IMP, Hemp in HsA.
                apply HsA.
             ++ eapply MA, HmF. 1,2:eassumption.
                reflexivity.
        * intro y.
          case (MB y) as [(_ & ->) | (x & Fx & Mx & _)];
            [left; reflexivity | right; eauto].
      + intro y.
        case (MB y) as [(-> & ->) | (x & _ & <- & IMP)].
        * cbn; reflexivity.
        * apply IMP, HsA.
    - eenough (P_ex1 : _).
      unshelve epose proof (ms_pf := fun y => FMem.of_pred (UPred.mk (p := P y) (P_ex1 y)) _); cycle -1.
      exists (fun y => proj1_sig (ms_pf y)).
      apply (fun y => proj2_sig (ms_pf y)).
      + cbn; unfold P.
        intros ? ? E.
        setoid_rewrite E; auto.
      + intro y.
        apply ex1_intro2.
        * case (HB y) as [Ey | (x & Fx & IMP)].
          -- exists FMem.emp; left; intuition.
          -- exists (msA x); right; exists x; intuition.
        * intros m0 m1.
          apply P_unique; reflexivity.
  Qed.

  Lemma all_F [A B] (F : A -> B -> Prop) (eA : relation A) (eB : relation B)
    (hsA : A -> t) (hsB : B -> t)
    {eA_refl : Reflexive eA}
    {eB_refl : Reflexive eB}
    (HmF : forall (x x' : A) (y y' : B), F x y -> F x' y' -> eA x x' <-> eB y y')
    (HmA : forall (x x' : A), eA x x' -> SLprop.eq (hsA x) (hsA x'))
    (HmB : forall (y y' : B), eB y y' -> SLprop.eq (hsB y) (hsB y'))
    (HE  : forall (x : A) (y : B), F x y -> SLprop.eq (hsA x) (hsB y))
    (HF  : forall x : A, SLprop.eq (hsA x) emp \/ exists y : B, F x y)
    (HB  : forall y : B, SLprop.eq (hsB y) emp \/ exists x : A, F x y):
    SLprop.eq (all eA hsA) (all eB hsB).
  Proof.
    apply eq_iff_imp; split.
    - apply all_F_imp with (F := F); auto.
      + intro x; case (HF x) as [Ex|(y & Fx)];
          [left|right;exists y]; intuition.
        apply eq_imp, HE, Fx.
      + intro y; case (HB y) as [Ey|(x & Fx)];
          [left|right; exists x]; intuition.
        apply eq_imp, HE, Fx.
    - apply all_F_imp with (F := fun y x => F x y); eauto.
      + intros; symmetry; apply HmF; auto.
      + intro y; case (HB y) as [Ey|(x & Fx)];
          [left|right;exists x]; intuition.
        apply eq_imp; symmetry; apply HE, Fx.
      + intro x; case (HF x) as [Ex|(y & Fx)];
          [left|right;exists y]; intuition.
        apply eq_imp; symmetry; apply HE, Fx.
  Qed.

  Definition all_sub [A : Type] (eA : relation A) (P : A -> Prop) (hs : A -> t) : t :=
    @all (sig P) (fun x0 x1 => eA (proj1_sig x0) (proj1_sig x1)) (fun x => hs (proj1_sig x)).

  Section All_Group.
    Context [A B] (G : B -> A -> Prop) (eA : relation A) (eB : relation B) (hs : A -> SLprop.t)
      {eA_eqv : Equivalence eA}
      {eB_eqv : Equivalence eB}
      (PART   : forall x : A, ex1 eB (fun y => G y x))
      (eB_EM  : forall y0 y1, eB y0 y1 \/ ~eB y0 y1)
      (G_EM   : forall x y, G y x \/ ~G y x)
      (HmG    : forall y0 y1 (Ey : eB y0 y1) x0 x1 (Ex : eA x0 x1), G y0 x0 -> G y1 x1).

    Local Add Morphism G
      with signature eB ==> eA ==> iff
      as HmG_morph.
    Proof. symmetric_iff; exact HmG. Qed.

    Let all_g := @all B eB (fun y => all_sub eA (G y) hs).
    
    Lemma all_group: SLprop.imp (@all A eA hs) all_g.
    Proof.
      intros m (ms & Me & J & Hs).
      apply FMem.is_join_set_group with (G := G) (eB := eB) in J as (msG & J & Js); auto.
      exists msG; splits.
      - intros y y' HG; eapply FMem.is_join_set_unique, Js.
        + do 2 intro; apply Me.
        + assert (G_iff : forall x, G y x <-> G y' x)
            by (setoid_rewrite HG; reflexivity).
          generalize (Js y); apply FMem.is_join_set_F with (F := fun x x' => proj1_sig x = proj1_sig x').
          1:congruence.
          1,2:
            intros [x0 Gx];
            right; unshelve eexists (exist _ x0 _);
            [ apply G_iff, Gx | cbn; intuition ].
      - exact J.
      - intro y.
        exists (fun x => ms (proj1_sig x)); splits.
        + do 2 intro; apply Me.
        + apply Js.
        + intro; apply Hs.
    Qed.

    Section Choosable_G.
      Import List ListNotations UPred.

      Definition valid_pred (y : B) (P : (sig (G y) -> FMem.t) -> Prop) : Prop :=
        forall f0 f1 (E : forall x', FMem.eq (f0 x') (f1 x')), P f0 -> P f1.

      Definition valid_partial_f (y : B) (f : sig (G y) -> FMem.t) : Prop :=
        forall x0 x1, proj1_sig x0 = proj1_sig x1 -> FMem.eq (f x0) (f x1).

      Definition choosable_G : Prop :=
        forall
          (P  : forall (y : B) (f : sig (G y) -> FMem.t), Prop)
          (M  : forall y, valid_pred y (P y))
          (EX : forall y, exists f, valid_partial_f y f /\ P y f),
        exists f : A -> FMem.t,
          forall y0, exists y, eB y0 y /\ P y (fun x => f (proj1_sig x)).

      (* [finite_choosable] *)

      Fixpoint is_first [C] (P : C -> Prop) (xs : list C) (x : sig P) {struct xs} : Prop :=
        match xs with
        | nil      => False
        | hd :: tl =>
            (exists pf : P hd, x = exist P hd pf) \/
            (~P hd /\ is_first P tl x)
        end.

      Lemma is_first_morph [C P0 P1]
        (E : forall x : C, P0 x <-> P1 x)
        xs x:
        is_first P0 xs x ->
        exists pf,
        is_first P1 xs (exist P1 (proj1_sig x) pf).
      Proof.
        induction xs.
        - intros [].
        - intros [[pf0 ->]|[nP0 F0]]; cbn.
          + unshelve eexists. apply E, pf0.
            left; eauto.
          + case (IHxs F0) as [pf1 F1].
            exists pf1; right; intuition.
            apply nP0, E; auto.
      Qed.

      Lemma is_first_ex1 [C P]
        (P_em : forall x, P x \/ ~P x):
        forall [xs] (HE : List.Exists P xs),
        ex1 (fun x0 x1 => proj1_sig x0 = proj1_sig x1) (@is_first C P xs).
      Proof.
        eenough _ as case_Here.
        induction 1 as [hd tl HP|hd tl _ IH].
        2:case (P_em hd) as [HP|HnP].
        all:swap 3 4.
        - revert hd tl HP; exact case_Here.
        - apply case_Here; auto.
        - intros hd tl HP.
          exists (exist _ hd HP); split.
          + left; eauto.
          + intros ? [[? ->]|[ABS _]]; tauto.
        - case IH as (x & Ex & Ux).
          exists x; split.
          + right; auto.
          + intros ? [[ABS _]|[_ F]]; intuition.
      Qed.

      Lemma finite_choosable
        (ys : list B)
        (R : forall y, List.Exists (eB y) ys):
        choosable_G.
      Proof.
        intros P M EX.
        rename ys into ys0.
        pose (VP y f := valid_partial_f y f /\ P y f).
        assert (exists ys : list {y & {f | VP y f}}, List.map (@projT1 _ _) ys = ys0) as [ys YS]. {
          clear R.
          induction ys0 as [|hd tl].
          - exists nil; reflexivity.
          - case (EX hd) as (hd_f & hd_P).
            case IHtl as (ys & <-).
            unshelve eexists (cons _ ys).
            + exists hd, hd_f. exact hd_P.
            + reflexivity.
        }
        assert (Ry : forall y, List.Exists (fun y' => eB y (projT1 y')) ys). {
          intro y.
          generalize (R y).
          rewrite <- YS, List.Exists_map.
          auto.
        }
        clear ys0 R EX YS.
        unshelve epose (get_r y := UPred.mk (is_first_ex1 _ (Ry y))).
          { cbn; intro; apply eB_EM. }
        cbn in get_r.
        assert (get_r_morph : forall y0 y1 (Ey : eB y0 y1) y,
                get_r y0 y ->
                exists pf, get_r y1 (exist _ (proj1_sig y) pf)). {
          unfold get_r; cbn; do 4 intro.
          refine (is_first_morph _ ys y).
          setoid_rewrite Ey; reflexivity.
        }
        clearbody get_r.
        unshelve pose proof (get_y := fun x => UPred.mk_s (PART x)).
        assert (mP_G_pf : forall x y0 y, eB y0 y -> G y0 x -> G y x). {
          intros ? ? ? ->; auto.
        }
        unshelve epose (mP x (m : FMem.t) := 'y0 := get_y x in 'y := get_r (proj1_sig y0) in FMem.eq m _). {
          case y0 as [y0 Gx].
          case y  as [[y [f ?]] Ey]; cbn in Ey.
          refine (f (exist _ x (mP_G_pf _ _ _ Ey Gx))).
        }
        cbn in mP.
        assert (forall x, ex1 FMem.eq (mP x)) as mP_ex1. {
          intro x; unfold mP.
          case (UPred.Get_bind_e (get_y x)) as [[y Gy] Y].
          setoid_rewrite Y; clear Y. 2:{
            intros [y']; cbn.
            intros Ey H y0' Get_r'.
            apply get_r_morph with (y1 := y) in Get_r' as [? Get_r].
              2:{ symmetry; exact Ey. }
            specialize (H _ Get_r); cbn in H; rewrite H.
            case y0' as [[y1 [f Vf]] ?]; cbn.
            apply Vf; reflexivity.
          }
          cbn.
          case (UPred.Get_bind_e (get_r y)) as [[y0 Ey] Yr].
          setoid_rewrite Yr; clear Yr. 2:{
            cbn; intros [[y1 [f Vf]] ?]; intros -> ->; cbn.
            apply Vf; reflexivity.
          }
          do 2 esplit. reflexivity.
          intros ? ->; reflexivity.
        }
        unshelve epose proof (f_pf := fun x => FMem.of_pred (UPred.mk (mP_ex1 x)) _). {
          unfold mP; cbn.
          intros ? ? Em.
          setoid_rewrite Em.
          auto.
        }
        exists (fun x => proj1_sig (f_pf x)).
        intro y0.
        case (UPred.unq (get_r y0)) as [[[y [f Vf]] Ey] [Get_r _]]; cbn in *.
        exists y; split. exact Ey.
        eapply M, Vf.
        intros [x' Gx']; cbn.
        case (f_pf x') as [m' mP']; cbn.
        unfold mP, UPred.bind in mP'.
        case (UPred.unq (get_y x')) as ([y1 Gy1] & get_y1 & _); cbn in *.
        specialize (mP' _ get_y1).
        apply get_r_morph with (y1 := y1) in Get_r as [? Get_r1].
          2:{ rewrite Ey.
              refine (ex1_unique _ (PART x') _ _ Gx' Gy1).
              intros ? ? ->; auto. }
        specialize (mP' _ Get_r1); cbn in mP'; rewrite mP'.
        apply Vf; reflexivity.
      Qed.
    End Choosable_G.

    Hypothesis G_chs : choosable_G.

    Lemma choose_on_G
        [P  : forall (y : B) (f : sig (G y) -> FMem.t), Prop]
        (M0 : forall y, valid_pred y (P y))
        (M1 : forall y0 y1 (f : A -> FMem.t), eB y0 y1 ->
              P y0 (fun x => f (proj1_sig x)) -> P y1 (fun x => f (proj1_sig x)))
        (EX : forall y, exists f, valid_partial_f y f /\ P y f):
      exists f : A -> FMem.t,
        forall y, P y (fun x => f (proj1_sig x)).
    Proof.
      case (G_chs _ M0 EX) as [f H].
      exists f.
      intro y0.
      case (H y0) as (y1 & Ey & H1).
      eapply M1, H1.
      symmetry; exact Ey.
    Qed.

    Lemma all_ungroup: SLprop.imp all_g (@all A eA hs).
    Proof.
      intros m (msG & MeG & JG & HsG); cbn in HsG.
      eassert (HsG' : forall y : B, exists ms : sig (G y) -> FMem.t,
                      valid_partial_f y ms /\ _). {
        intro y.
        case (HsG y) as [ms H].
        exists ms; split. 2:exact H.
        intros x0 x1 Eq; apply H.
        rewrite Eq; reflexivity.
      }
      clear HsG.
      eenough _ as M1. eenough _ as M0.
      case (choose_on_G M0 M1 HsG') as [ms MS]; clear HsG' M0 M1.
      2:{
        intros y ms0 ms1 Em.
        setoid_rewrite Em.
        intuition.
        eapply FMem.is_join_set_morph; [..|eassumption]; try reflexivity.
        - symmetry; exact Em.
      }
      2:{
        cbn; intros y0 y1 f Ey (H0 & H1 & H2).
        splits.
        - intros [x0'] [x1'].
          refine (H0 (exist _ x0' _) (exist _ x1' _));
          rewrite Ey; auto.
        - rewrite <- (MeG _ _ Ey).
          eapply FMem.is_join_set_F with (F := fun x0' x1' => proj1_sig x0' = proj1_sig x1'), H1.
          1:congruence.
          1,2:
            intros [x Gx];
            right; unshelve eexists (exist _ x _);
            [ revert Gx; rewrite Ey; auto | cbn; intuition ].
        - intros [x].
          refine (H2 (exist _ x _)).
          rewrite Ey; auto.
      }
      assert (Me : forall x x', eA x x' -> FMem.eq (ms x) (ms x')). {
        intros x x' Ex.
        case (PART x) as (y & Gx & _).
        case (MS y) as (H & _).
        refine (H (exist _ x _) (exist _ x' _) Ex);
          rewrite <-?Ex; exact Gx.
      }
      exists ms; splits.
      - exact Me.
      - apply FMem.is_join_set_ungroup with (G := G) (eB := eB) (msG := msG); auto.
        intro y; apply (MS y).
      - intro x.
        case (PART x) as (y & Gx & _).
        case (MS y) as (_ & _ & H).
        refine (H (exist _ x Gx)).
    Qed.

    Lemma all_group_eq: SLprop.eq (@all A eA hs) all_g.
    Proof.
      apply eq_iff_imp; auto using all_group, all_ungroup.
    Qed.
  End All_Group. 

  Lemma all_2 h0 h1:
    SLprop.eq (@all bool Logic.eq (fun b => if b then h0 else h1)) (h0 ** h1).
  Proof.
    intro m; split.
    - intros (ms & _ & J & Hs).
      eapply FMem.is_join_set_morph, FMem.is_join_set_2 in J;
        try reflexivity.
        2:{ intros []; reflexivity. }
      do 3 esplit. exact J.
      split. apply (Hs true). apply (Hs false).
    - intros (m0 & m1 & J & H0 & H1).
      exists (fun b : bool => if b then m0 else m1).
      split; [|split].
      + intros ? ? ->; reflexivity.
      + apply FMem.is_join_set_2, J.
      + intros []. apply H0. apply H1.
  Qed.

  Lemma all_0 A e hs
    {e_refl : Reflexive e}
    (Emp : forall x : A, SLprop.eq (hs x) emp):
    SLprop.eq (@all A e hs) emp.
  Proof.
    setoid_rewrite <- star_emp_l at 2.
    setoid_rewrite <- all_2.
    eapply all_F with (F := fun _ _ => False);
      intuition subst; auto.
    - rewrite !Emp; reflexivity.
    - reflexivity.
    - left; case y; reflexivity.
  Qed.

  Lemma all_1_unit h:
    SLprop.eq (@all unit Logic.eq (fun _ => h)) h.
  Proof.
    setoid_rewrite <- star_emp_r at 3.
    setoid_rewrite <- all_2.
    apply all_F with (F := fun _ b => b = true);
      intuition subst; auto; try reflexivity.
    - case x, x'; reflexivity.
    - right; eauto.
    - case y.
      + right; exists tt; reflexivity.
      + left; reflexivity.
  Qed.

  Lemma all_1 (h : t) [A] (eA : relation A) (hs : A -> t)
    (U : forall x0 x1, eA x0 x1)
    (H : forall x, SLprop.eq (hs x) h)
    (E : inhabited A):
    SLprop.eq (@all A eA hs) h.
  Proof.
    etransitivity. 2:apply all_1_unit.
    apply all_F with (F := fun _ _ => True); auto.
    - intros ? ? [] []; intuition.
    - intros; rewrite !H; reflexivity.
    - reflexivity.
    - right; exists tt; split.
    - right; case E as [x]; eauto.
  Qed.


  Lemma all_split [A] (f : A -> bool) (eA : relation A) (hs : A -> t)
    {eA_eqv : Equivalence eA}
    {HmF : forall x0 x1, eA x0 x1 -> f x0 = f x1}:
    SLprop.eq (@all A eA hs)
              (all_sub eA (fun x => f x = true) hs ** all_sub eA (fun x => f x = false) hs).
  Proof.
    rewrite <- all_2.
    etransitivity.
    - eenough _ as H0. eenough _ as H1.
      apply all_group_eq with (G := fun b x => f x = b) (eB := @Logic.eq bool);
        auto_tc.
      + eexists; eauto.
      + exact H0.
      + intros x b; case (Bool.bool_dec (f x) b); eauto.
      + exact H1.
      + apply finite_choosable with (eA := eA) (ys := cons false (cons true nil));
          auto_tc.
        * eexists; eauto.
        * intros []; [right;left|left]; reflexivity.
      + intros ? ? -> ? ? ->%HmF; auto.
      + intros b0 b1; case (Bool.bool_dec b0 b1); eauto.
    - apply all_F with (F := @Logic.eq bool);
        auto_tc; eauto.
      1,2,3:intuition subst; auto; try reflexivity.
      + intros ? b ->; case b; reflexivity.
  Qed.

  Lemma all_sub_conj [A] (eA : relation A) (P0 : A -> Prop) (P1 : A -> Prop) (hs : A -> t)
    {_ : Reflexive eA}
    (HmH : forall x0 x1, eA x0 x1 -> SLprop.eq (hs x0) (hs x1)):
    SLprop.eq
      (@all {x : sig P0 | P1 (proj1_sig x)}
            (fun x0 x1 => eA (proj1_sig (proj1_sig x0)) (proj1_sig (proj1_sig x1)))
            (fun x => hs (proj1_sig (proj1_sig x))))
      (@all_sub A eA (fun x => P0 x /\ P1 x) hs).
  Proof.
    apply all_F with (F := fun x y => proj1_sig (proj1_sig x) = proj1_sig y); auto.
    - intros [[]] [[]] [] [] -> ->; cbn; reflexivity.
    - intros [[]] [] ->; cbn; reflexivity.
    - intros [[x]]; right.
      unshelve eexists (exist _ x _); cbn; auto.
    - intros [x []]; right.
      unshelve eexists (exist _ (exist _ x _) _); cbn; auto.
  Qed.

  Lemma all_sub_iff [A] (eA : relation A) (P0 : A -> Prop) (P1 : A -> Prop) (hs : A -> t)
    {_ : Reflexive eA}
    (HmH : forall x0 x1, eA x0 x1 -> SLprop.eq (hs x0) (hs x1))
    (P_iff : forall x, P0 x <-> P1 x):
    SLprop.eq (all_sub eA P0 hs) (all_sub eA P1 hs).
  Proof.
    apply all_F with (F := fun x y => proj1_sig x = proj1_sig y); auto.
    3,4:intros [x]; right; unshelve eexists (exist _ x _); cbn; auto;
        apply P_iff; auto.
    - intros [] [] [] [] -> ->; cbn; reflexivity.
    - intros [] [] ->; cbn; reflexivity.
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
      - (* RIPureTrue *) unfold pure; intro; cbn; tauto.
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
