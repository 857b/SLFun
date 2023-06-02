From SLFun Require Import Util Values SL VProg.Vprop VProg.Core.
From Coq   Require Import Lists.List.

Import SLNotations ListNotations VProg.Vprop.Notations VProg.Core.Notations VProg.Core.Abbrev.
Import SL.Tactics VProg.Core.Tactics.


Section Admit.
  Lemma admit_change {A} : @ghost_lem (mk_f_sig (VpropList.t * (A -> VpropList.t)) A)
    (fun '(V0, V1) _ =>
     Spec.mk_r0 (Tuple.force_match (VpropList.sel V0) (fun sel0 =>
     Spec.mk_r1 (GO := None) [] (VpropList.inst V0 sel0) False (fun x =>
     Spec.mk_r2 _ (V1 x) (Tuple.of_fun (fun sel1 _ =>
     Spec.mk_r3 _ sel1 True)))))).
  Proof.
    init_lemma (?, ?) ?.
    rewrite Tuple.to_of_fun; intros [].
  Qed.
End Admit.
Section Equivalence.
  Variables (V0 V1 : VpropList.t).
  Section Proof.
    Variables (f : VpropList.sel_t V0 -> VpropList.sel_t V1) (g : VpropList.sel_t V1 -> VpropList.sel_t V0).

    Definition eqv_lem1_spec : ghost_spec (mk_f_sig unit unit) :=
      fun _ _ =>
      Spec.mk_r0 (Tuple.force_match (VpropList.sel V0) (fun sel0 =>
      Spec.mk_r1 [] (VpropList.inst V0 sel0) True (fun _ =>
      Spec.mk_r2 [] V1 (fun _ =>
      Spec.mk_r3 _ (f sel0) True)))).
    
    Definition eqv_lem2_spec : ghost_spec (mk_f_sig unit unit) :=
      fun _ _ =>
      Spec.mk_r0 (Tuple.force_match (VpropList.sel V1) (fun sel1 =>
      Spec.mk_r1 [] (VpropList.inst V1 sel1) True (fun _ =>
      Spec.mk_r2 [] V0 (fun _ =>
      Spec.mk_r3 _ (g sel1) True)))).

    Hypothesis (GF : forall x, g (f x) = x)
               (E : forall y, SLprop.eq (CTX.sl (VpropList.inst V0 (g y))) (CTX.sl (VpropList.inst V1 y))).
 
    Lemma eqv_lem1 : ghost_lem eqv_lem1_spec.
    Proof.
      init_lemma _ sel0.
      rewrite Tuple.to_of_fun.
      intro; SL.normalize.
      rewrite !List.app_nil_r, <-E, GF.
      reflexivity.
    Qed.
    
    Lemma eqv_lem2 : ghost_lem eqv_lem2_spec.
    Proof.
      init_lemma _ sel1.
      rewrite Tuple.to_of_fun.
      intro; SL.normalize.
      rewrite !List.app_nil_r, E.
      reflexivity.
    Qed.
  End Proof.

  Variables
    (f : Tuple.arrow (VpropList.sel V0) (fun _ => Tuple.u_t (VpropList.sel V1)))
    (g : Tuple.arrow (VpropList.sel V1) (fun _ => Tuple.u_t (VpropList.sel V0))).

  Let f' x := Tuple.of_u_t (Tuple.to_fun f x).
  Let g' x := Tuple.of_u_t (Tuple.to_fun g x).

  Definition eqv_lemma : Prop :=
    ghost_lem (eqv_lem1_spec f') /\ ghost_lem (eqv_lem2_spec g').

  Lemma intro_eqv_lemma
    (GF : Tuple.arrow (VpropList.sel V0) (fun sel0 => g' (f' sel0) = sel0))
    (E  : Tuple.arrow (VpropList.sel V1) (fun sel1 =>
            SLprop.eq (CTX.sl (VpropList.inst V0 (g' sel1)))
                      (CTX.sl (VpropList.inst V1 sel1))))
    : eqv_lemma.
  Proof.
    specialize (Tuple.to_fun GF) as GF'.
    specialize (Tuple.to_fun  E) as E'.
    split; eauto using eqv_lem1, eqv_lem2.
  Qed.

  Definition gUnfold {CT} (L : eqv_lemma) : @instr CT unit :=
    gLem (proj1 L) tt.
  Definition gFold {CT} (L : eqv_lemma) : @instr CT unit :=
    gLem (proj2 L) tt.
End Equivalence.
Global Arguments gUnfold [_ _ _ _] {_} L.
Global Arguments gFold   [_ _ _ _] {_} L.
Section Replace.
  Definition replace1_spec A : LDecl SPEC
    ((v0, v1) : Vprop.p A * Vprop.p A) 'x [] [v0 ~> x] (v0 = v1)
    '(_ : unit) tt [v1 ~> x] True.
  Proof. Derived. Defined.
  Lemma replace1 {A} : replace1_spec A.
  Proof.
    init_lemma (v0, v1) sel0 E; subst; reflexivity.
  Qed.

  Definition replace (V0 V1 : VpropList.t) : @ghost_lem (mk_f_sig (VpropList.sel V0 = VpropList.sel V1) unit)
    (fun E _ =>
     Spec.mk_r0 (Tuple.force_match (VpropList.sel V0) (fun sel0 =>
     Spec.mk_r1 [] (VpropList.inst V0 sel0)
       (eq_rect _ (fun st => Tuple.t st -> CTX.t) (VpropList.inst V0) _ E = VpropList.inst V1) (fun _ =>
     Spec.mk_r2 [] V1 (fun _ =>
     Spec.mk_r3 _ (eq_rect _ Tuple.t sel0 _ E) True))))).
  Proof.
    init_lemma E sel0.
    rewrite Tuple.to_of_fun; cbn.
    intros <-.
    SL.normalize.
    destruct E; cbn; reflexivity.
  Qed.
End Replace.
Section Impp.
  Context [sel_t A : Type] (spc : sel_t -> (CTX.t * Prop * (A -> Prop))).

  Definition impp_lemma_spec : ghost_spec (mk_f_sig unit A) :=
    fun _ _ =>
    Spec.mk_r0 (fun (sel : sel_t) => let '(sl, pre, post) := spc sel in
    Spec.mk_r1 (GO := None) sl [] pre (fun (x : A) =>
    Spec.mk_r2 [] [] (fun _ =>
    Spec.mk_r3 [] tt (post x)))).

  Definition impp_lemma := ghost_lem impp_lemma_spec.

  Lemma intro_impp_lemma
    (H : forall sel : sel_t, let '(sl, pre, post) := spc sel in
         pre -> SLprop.impp (CTX.sl sl) (exists x : A, post x)):
    impp_lemma.
  Proof.
    unfold impp_lemma.
    init_lemma [] sel PRE.
    specialize (H sel).
    destruct (spc sel) as ((sl, pre), post); cbn in *.
    SL.normalize.
    eapply SLprop.cut_pure. apply H, PRE.
    intros [x POST].
    Apply x.
    Apply POST.
    reflexivity.
  Qed.
End Impp.
Section Exploit.
  Context [CT : CP.context] (vs : VpropList.t).

  Definition exploit_hyp (sel : VpropList.sel_t vs) : Prop :=
    forall P : Prop, SLprop.impp (CTX.sl (VpropList.inst vs sel)) P -> P.

  Definition exploit_spec : ghost_spec (mk_f_sig unit unit) :=
    fun _ _ =>
    Spec.mk_r0 (Tuple.force_match (VpropList.sel vs) (fun sel =>
    Spec.mk_r1 (GO := None) (VpropList.inst vs sel) [] True (fun _ =>
    Spec.mk_r2 [] [] (fun _ =>
    Spec.mk_r3 [] tt (exploit_hyp sel))))).
  Lemma exploit_correct : ghost_lem exploit_spec.
  Proof.
    init_lemma [] sel.
    rewrite Tuple.to_of_fun; cbn; intro.
    SL.normalize.
    eapply SLprop.cut_pure. 2:intro H; Apply H; reflexivity.
    unfold exploit_hyp.
    intros m M P I; eapply I, M.
  Qed.

  Definition gExploit : instr CT unit := gLem exploit_correct tt.
End Exploit.

Section GGet.
  Context [CT : CP.context] [A : Type] (v : Vprop.p A).

  Inductive GGet_Spec (ctx : CTX.t) (F : i_spec_t A ctx) : Prop
    := GGet_SpecI
    (a : A)
    (IJ : InjPre_Frame_Spec [CTX.mka (v, a)] ctx {|
      sf_csm  := Vector.cons _ false _ (Vector.nil _) <: Sub.t [_];
      sf_prd  := fun _ => nil;
      sf_spec := FP.Ret (TF.mk0 _ a Tuple.tt)
    |} F).

  Program Definition gGet : instr CT A := {|
    i_impl := CP.Oracle A;
    i_spec := fun ctx => GGet_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_Frame IJ); clear IJ.
    do 2 intro; cbn in *.
    apply SP.COracle with (x := a).
    Apply tt.
    Apply PRE.
    reflexivity.
  Qed.
End GGet.

Local Ltac build_GGet :=
  simple refine (GGet_SpecI _ _ _ _ _);
  [ shelve | Tac.build_InjPre_Frame ].

Section Assert.
  Context [CT : CP.context] [A : Type] (P : A -> CTX.t * Prop).

  Inductive Assert_Spec (ctx : CTX.t) (F : i_spec_t unit ctx) : Prop
    := Assert_SpecI
    (p : A)
    (IJ : InjPre_Frame_Spec (fst (P p)) ctx {|
      sf_csm  := Sub.const (fst (P p)) false;
      sf_prd  := fun _ => nil;
      sf_spec := FP.Bind (FP.Assert (snd (P p)))
                         (TF.of_fun (fun _ => FP.Ret (TF.mk0 _ tt Tuple.tt)))
    |} F).
  
  Program Definition Assert : instr CT unit := {|
    i_impl := SP.sl_assert (SLprop.ex A (fun p =>
                SLprop.pure (snd (P p)) ** CTX.sl (fst (P p))))%slprop;
    i_spec := fun ctx => Assert_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_Frame IJ); clear IJ.
    do 2 intro; cbn in *.
    case PRE as (PRE & POST).
    eapply SP.Cons.
    - apply SP.Assert_imp with (Q := CTX.sl (fst (P p))).
      Apply p.
      Apply PRE.
      reflexivity.
    - split; cbn.
      + reflexivity.
      + intros []; SL.normalize.
        Apply POST.
        unfold Sub.neg, Sub.const;
          rewrite Vector.map_const, Sub.sub_const_true.
        reflexivity.
  Qed.
End Assert.

Local Ltac build_Assert :=
  simple refine (Assert_SpecI _ _ _ _ _);
  [ shelve
  | (* IJ *)
    cbn;
    (* [p : A] can be a tuple let-matched by [P] *)
    repeat lazymatch goal with |- InjPre_Frame_Spec (fst ?x) _ _ _ =>
      Tac.build_matched_shape x; cbn
    end;
    Tac.build_InjPre_Frame ].

Module Tactics.
  #[export] Hint Extern 1 (GGet_Spec    _ _ _) => build_GGet   : HasSpecDB.
  #[export] Hint Extern 1 (Assert_Spec  _ _ _) => build_Assert : HasSpecDB.
End Tactics.
Export Tactics.
