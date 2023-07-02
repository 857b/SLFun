From SLFun Require Export Values.
From SLFun Require Import Util SL.
From SLFun Require ConcreteProg.
From Coq   Require Import Setoids.Setoid.

Module CP := ConcreteProg.
Import SLNotations.
Open Scope slprop.


Module Spec. Section Spec.
  Local Set Implicit Arguments.
  Variable A : Type.

  Record t := mk {
    pre  : SLprop.t;
    post : A -> SLprop.t;
  }.

  Definition eq (s0 s1 : t) :=
    SLprop.eq (pre s0) (pre s1) /\ forall x : A, SLprop.eq (post s0 x) (post s1 x).

  Definition le (s0 s1 : t) :=
    SLprop.imp (pre s1) (pre s0) /\ forall x : A, SLprop.imp (post s0 x) (post s1 x).

  Global Instance spec_PartialOrder : Rel.MakePartialOrder eq le.
  Proof.
    split.
    - intros ? ?; cbn.
      unfold Basics.flip, eq, le.
      setoid_rewrite (Rel.partial_order_eq_iff SLprop.eq SLprop.imp).
      setoid_rewrite Rel.forall_and_comm.
      tauto.
    - Rel.by_expr (Rel.conj (Rel.pull pre (Basics.flip SLprop.imp)) (Rel.pull post (Rel.point A SLprop.imp))).
      eauto 8 with typeclass_instances.
  Qed.

  Global Add Morphism mk
    with signature SLprop.eq ==> Morphisms.pointwise_relation A SLprop.eq ==> eq
    as mk_morph.
  Proof.
    intros ? ? E0 ? ? E1; exact (conj E0 E1).
  Qed.

  Definition frame (s : t) (fr : SLprop.t) : t := {|
    pre  := pre s ** fr;
    post := fun x => post s x ** fr;
  |}.

  Definition tr (s : t): CP.Spec.t A := {|
    CP.Spec.pre  := SLprop.mem_match (pre s);
    CP.Spec.post := fun _ r => SLprop.mem_match (post s r);
  |}.

  Definition wp_match (s : t) (wp : CP.Spec.wp_t A): Prop :=
    forall fr, CP.Spec.wp_impl wp (tr (frame s fr)).

  Definition spec_match (s : t) (t : CP.Spec.t A -> Prop): Prop :=
    forall fr, exists t_s, t t_s /\ CP.Spec.le t_s (tr (frame s fr)).
End Spec. End Spec.

Section F_SPEC.
  Local Set Implicit Arguments.
  Variable sg : f_sig.

  Definition f_spec :=
    f_arg_t sg -> Spec.t (f_ret_t sg) -> Prop.

  Definition match_f_spec (s : f_spec) (t : CP.f_spec sg) : Prop :=
    forall x s_s, s x s_s -> Spec.spec_match s_s (t x).

  Definition tr_f_spec (s : f_spec) : CP.f_spec sg :=
    fun x t_s => exists s_s fr, s x s_s /\ t_s = Spec.tr (Spec.frame s_s fr).

  Lemma tr_f_spec_match (s : f_spec):
    match_f_spec s (tr_f_spec s).
  Proof.
    intros x s_s S fr; do 2 esplit.
    - exists s_s, fr; eauto.
    - reflexivity.
  Qed.

  Lemma wp_impl_tr_f_spec [sp : f_spec] [x wp]
    (IM : forall s (SP : sp x s), Spec.wp_match s wp)
    s (TR : tr_f_spec sp x s):
    CP.Spec.wp_impl wp s.
  Proof.
    case TR as (? & fr & SP & ->).
    apply IM, SP.
  Qed.
End F_SPEC.

Section SLS. 
  Context [SG : sig_context] (SPC : CP.spec_context SG).

  (* Separation Logic Spec *)
  Definition sls [A] (i : CP.instr A) (s : Spec.t A) : Prop :=
    Spec.wp_match s (CP.wlp SPC i).

  Lemma sls_morph_imp [A] (i : CP.instr A) (s0 s1 : Spec.t A) (LE : Spec.le s0 s1):
    sls i s0 -> sls i s1.
  Proof.
    intros SLS fr m0; simpl; intro M0.
    eapply CP.wlp_monotone, SLS with (fr := fr); cycle 1; simpl.
    - eapply SLprop.mem_match_morph_imp, M0.
      apply SLprop.star_morph_imp; [apply LE|reflexivity].
    - intros x m1.
      apply SLprop.mem_match_morph_imp, SLprop.star_morph_imp; [apply LE|reflexivity].
  Qed.

  Global Add Parametric Morphism A i : (@sls A i)
    with signature (@Spec.eq A) ==> iff
    as sls_morph.
  Proof.
    symmetric_iff.
    intros s0 s1 E.
    apply sls_morph_imp.
    rewrite E; reflexivity.
  Qed.

  (* Constructors *)
  
  (** Proof *)

  Section ProofRules.
    Context [A : Type] (f : @CP.instr SG A).

    Lemma Cons [s0 s1 : Spec.t A] (Sf : sls f s0) (LE : Spec.le s0 s1):
      sls f s1.
    Proof.
      eapply sls_morph_imp; eauto.
    Qed.

    Lemma Frame [s : Spec.t A] (Sf : sls f s) (fr : SLprop.t):
      sls f (Spec.frame s fr).
    Proof.
      intros fr' m0; simpl.
      setoid_rewrite SLprop.star_assoc at 1.
      intros M0; eapply CP.wlp_monotone, Sf with (fr := (fr ** fr')); auto.
      simpl; setoid_rewrite SLprop.star_assoc; auto.
    Qed.

    Lemma CFrame [s0 s1 : Spec.t A] (Sf : sls f s0) (fr : SLprop.t) (LE : Spec.le (Spec.frame s0 fr) s1):
      sls f s1.
    Proof.
      eapply Cons, LE.
      eapply Frame, Sf.
    Qed.

    Lemma PureE (P : Prop) (pre : SLprop.t) (post : A -> SLprop.t)
      (Sf : P -> sls f (Spec.mk pre post)):
      sls f (Spec.mk (SLprop.pure P ** pre) post).
    Proof.
      intros fr m0; simpl; intros (fm0 & FM0 & H0).
      erewrite SLprop.sl_pred_eq in H0 by SL.normalize.
      apply SLprop.star_pure in H0 as (HP & H0).
      apply (Sf HP).
      exists fm0; eauto.
    Qed.

    Lemma ExistsE [X : Type] (pre : X -> SLprop.t) (post : A -> SLprop.t)
      (Sf : forall x : X, sls f (Spec.mk (pre x) post)):
      sls f (Spec.mk (SLprop.ex X pre) post).
    Proof.
      intros fr m0; simpl; intros (fm0 & FM0 & H0).
      erewrite SLprop.sl_pred_eq in H0 by SL.normalize.
      case H0 as (x & H0).
      apply (Sf x).
      exists fm0; eauto.
    Qed.
  End ProofRules.

  (** Instructions *)

  Section Ret.
    Context [A : Type] (x : A).

    Lemma Ret_SL (sp : A -> SLprop.t) : sls (CP.Ret x) (Spec.mk (sp x) sp).
    Proof.
      intros fr m0; simpl; auto.
    Qed.

    Lemma CRet (pre : SLprop.t) (post : A -> SLprop.t)
      (C : SLprop.imp pre (post x)):
      sls (CP.Ret x) (Spec.mk pre post).
    Proof.
      eapply Cons.
      apply (Ret_SL post).
      split. apply C. reflexivity.
    Qed.

    Lemma Ret (fr : SLprop.t) : sls (CP.Ret x) (Spec.mk fr (fun x' => SLprop.pure (x' = x) ** fr)).
    Proof.
      apply CRet, SLprop.imp_pure_r; reflexivity.
    Qed.
  End Ret. 
  Section Bind.
    Context [A B : Type]
      [pre : SLprop.t] [itm : A -> SLprop.t] [post : B -> SLprop.t]
      [f : CP.instr A] [g : forall x : A, CP.instr B]
      (Sf : sls f (Spec.mk pre itm)) (Sg : forall x : A, sls (g x) (Spec.mk (itm x) post)).

    Lemma Bind : sls (CP.Bind f (fun x => g x)) (Spec.mk pre post).
    Proof.
      intros fr m0; simpl; intros M0.
      eapply CP.wlp_monotone, Sf, M0.
      simpl; intros x.
      apply (Sg x).
    Qed.
  End Bind.
  Section Call.
    Context [sg : f_sig] (f : fid) (x : f_arg_t sg) (HSIG : SG f = Some sg) (s : Spec.t (f_ret_t sg)).

    Definition fun_has_spec :=
      Spec.spec_match s (CP.fun_has_spec SPC f HSIG x).
    Hypothesis (HSPC : fun_has_spec).

    Lemma Call : sls (CP.Call f HSIG x) s.
    Proof.
      intros fr m0; simpl; intro M0.
      case (HSPC fr) as (t_s & HS & SLE).
      exists t_s. split. exact HS.
      exact (SLE _ M0).
    Qed.
  End Call.
  Section Loop.
    Context [A B : Type] [inv : A + B -> SLprop.t]
      (ini : A + B)
      [f : A -> CP.instr (A + B)]
      (Sf : forall x : A, sls (f x) (Spec.mk (inv (inl x)) inv)).

    Lemma Loop : sls (CP.Loop ini f) (Spec.mk (inv ini) (fun x => inv (inr x))).
    Proof.
      intros fr m0; cbn; intros M0.
      exists (fun x => SLprop.mem_match (inv x ** fr)).
      split; [|split]; auto.
      - (* PRS *)
        intros x1 m1 M1.
        apply Sf, M1.
    Qed.
  End Loop.
  Section Oracle.
    Context [A : Type] (x : A).

    Lemma Oracle_SL (sp : A -> SLprop.t) : sls (CP.Oracle A) (Spec.mk (sp x) sp).
    Proof.
      exists x; auto.
    Qed.

    Lemma COracle (pre : SLprop.t) (post : A -> SLprop.t)
      (C : SLprop.imp pre (post x)):
      sls (CP.Oracle A) (Spec.mk pre post).
    Proof.
      eapply Cons.
      apply (Oracle_SL post).
      split. apply C. reflexivity.
    Qed.

    Lemma Oracle (fr : SLprop.t) : sls (CP.Oracle A) (Spec.mk fr (fun x' => SLprop.pure (x' = x) ** fr)).
    Proof.
      apply COracle, SLprop.imp_pure_r; reflexivity.
    Qed.
  End Oracle.
  Section Assert.
    Variable (P : SLprop.t).

    Definition sl_assert : @CP.instr SG unit :=
      CP.Assert (fun m => exists fr, SLprop.mem_match (P ** fr) m).

    Definition assert_spec (Q : SLprop.t) : Spec.t unit :=
      Spec.mk Q (fun _ => Q).

    Lemma Assert_imp Q (IMP : SLprop.imp Q P):
      sls sl_assert (assert_spec Q).
    Proof.
      intros fr m; simpl; intuition eauto.
      exists fr.
      eapply SLprop.mem_match_morph_imp; eauto.
      apply SLprop.star_morph_imp; auto; reflexivity.
    Qed.

    Lemma Assert : sls sl_assert (assert_spec P).
    Proof.
      apply Assert_imp; reflexivity.
    Qed.
  End Assert.
  Section Read.
    Variables (p : ptr) (d : memdata).

    Definition read_spec : Spec.t memdata := {|
      Spec.pre  := SLprop.cell p d;
      Spec.post := fun r => SLprop.cell p d ** SLprop.pure (r = d);
    |}.

    Lemma Read : sls (CP.Read p) read_spec.
    Proof.
      intros fr m; simpl; intro M0.
      case M0 as (fm & FM & M0).
      pose (M0' := M0); destruct M0' as (fm_cell & fm_frame & JOIN & (NNULL & CELL) & _).
      rewrite CELL in JOIN; clear CELL fm_cell.
      split. exact NNULL.
      do 2 esplit. exact FM.
      SL.normalize.
      eapply SLprop.star_pure; split; auto.
      - apply FM.
        generalize (JOIN p).
        unfold FMem.cell.
        case Mem.ptr_eq as []. 2:congruence.
        rewrite UPred.bind_one, UPred.p_iff_bind.
        do 2 UPred.auto_Get.
        inversion 1; reflexivity.
    Qed.
  End Read.
  Section Write.
    Variables (p : ptr) (d0 d1 : memdata).

    Definition write_spec : Spec.t unit := {|
      Spec.pre  := SLprop.cell p d0;
      Spec.post := fun _ => SLprop.cell p d1;
    |}.

    Lemma Write : sls (CP.Write p d1) write_spec.
    Proof.
      intros fr m; simpl; intros (fm0 & FM0 & fm_0 & fm_f & J0 & (NNULL & C0) & F0).
      split. exact NNULL.
      rewrite C0 in J0; clear C0 fm_0.
      exists (fset Mem.ptr_eq p (UPred.one (Some d1)) fm0).
      simpl; split.
      - intros q d; unfold Mem.write, fset.
        destruct Mem.ptr_eq. congruence. apply FM0.
      - exists (FMem.cell p d1), fm_f; intuition.
        intro q; generalize (J0 q).
        unfold FMem.cell, fset; case Mem.ptr_eq as [|]; auto.
        do 2 setoid_rewrite UPred.bind_one.
        do 2 UPred.auto_Get.
        inversion 1; constructor.
    Qed.
  End Write.

End SLS.

Module Tactics.
  #[export] Hint Extern 1 (Tac.Arrow _ (sls _ _ (Spec.mk _ _))) =>
    Tac.mk_Arrow_tac ltac:(fun _ =>
    eapply sls_morph; [eapply Spec.mk_morph; [|intro]; SLprop.Norm.normalize_core |])
      : NormalizeDB.
End Tactics.
