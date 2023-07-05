From SLFun Require Import Util Values SL VProg.Vprop VProg.Core.
From Coq   Require Import Lists.List.

Import SLNotations ListNotations VProg.Vprop.Notations VProg.Core.Notations VProg.Core.Abbrev.
Import SL.Tactics VProg.Core.Tactics.

Local Transparent FP.Bind FP.Ret FP.Call.

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
Section Rewrite.
  Definition rew_sel [v0 v1 : Vprop.t] (E : v0 = v1) (sel : Vprop.ty v0) : Vprop.ty v1 :=
    eq_rect v0 Vprop.ty sel v1 E.

  Inductive rewrite_ctx : forall (c0 : CTX.t), Sub.t c0 -> CTX.t -> Prop :=
    | RewCTX_Nil:
        rewrite_ctx [] Sub.nil []
    | RewCTX_Skip (a : CTX.atom)
        [c0 c1 : CTX.t] [s : Sub.t c0] (C : rewrite_ctx c0 s c1):
        rewrite_ctx (a :: c0) (Sub.cons false s) c1
    | RewCTX_NDep [A : Type] (v0 v1 : Vprop.p A) (E : v0 = v1) (sel : A)
        [c0 c1 : CTX.t] [s : Sub.t c0] (C : rewrite_ctx c0 s c1):
        rewrite_ctx ((v0 ~> sel) :: c0) (Sub.cons true s) ((v1 ~> sel) :: c1)
    | RewCTX_Dep (v0 v1 : Vprop.t) (E : v0 = v1) (sel : Vprop.ty v0)
        [c0 c1 : CTX.t] [s : Sub.t c0] (C : rewrite_ctx c0 s c1):
        rewrite_ctx (existT _ v0 sel :: c0) (Sub.cons true s) (existT _ v1 (rew_sel E sel) :: c1).

  Lemma rewrite_ctx_sl [c0 s c1]
    (R : rewrite_ctx c0 s c1):
    SLprop.eq (CTX.sl c0) (CTX.sl c1 ** CTX.sl (CTX.sub c0 (Sub.neg s))).
  Proof.
    induction R; cbn; SL.normalize; subst; try rewrite IHR; try reflexivity.
    - (* RewCTX_Skip *) apply SLprop.star_comm12.
  Qed.

  Context [CT : CP.context] [A : Type] (x y : A).

  Inductive Rewrite_Spec (ctx : CTX.t): forall (s : i_sig_t unit ctx), i_spec_t s -> Prop
    := Rewrite_SpecI
    [csm : Sub.t ctx] [c1 : forall E : x = y, CTX.t]
    (R : forall E : x = y, rewrite_ctx ctx csm (c1 E))
    [prd : VpropList.t]
    (PRD : forall E : x = y, prd = VpropList.of_ctx (c1 E)):
    let s := {|
      sf_csm  := csm;
      sf_prd  := fun _ => prd;
    |} in forall
    (f : i_spec_t s)
    (Ef : f = 
      FunProg.Bind (@FunProg.Call DTuple.unit {|
        FunProg.Spec.pre_p  := Some (x = y);
        FunProg.Spec.post_p := None;
      |}) (fun E =>
      FunProg.Ret (
        TF.mk _ tt (eq_rect_r VpropList.sel_t (VpropList.sel_of_ctx (c1 E)) (PRD E))
      ))),
    Rewrite_Spec ctx s f.

  Program Definition gRewrite : instr CT unit := {|
    i_impl := CP.Ret tt;
    i_spec := fun ctx => Rewrite_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; subst f; cbn in *.
    apply SP.CRet.
    case PRE as (E & PRE); specialize (PRE tt Logic.I); cbn in PRE.
    set (PRD' := PRD E) in *; clearbody PRD'; clear PRD.
    specialize (R E).
    set (c1' := c1 E) in *; clearbody c1'; clear c1.
    unfold eq_rect_r in PRE.
    destruct (eq_sym PRD').
    cbn in *.
    EApply. Apply PRE.
    apply rewrite_ctx_sl in R as ->.
    rewrite TF.to_of_tu, VpropList.inst_of_ctx, CTX.sl_app.
    reflexivity.
  Qed.
End Rewrite.
Global Arguments Rewrite_SpecI [A x y ctx csm c1] R [prd] PRD [f] Ef.

(* solves [E : x = y |- lhs = ?rhs] by rewriting [E] in [lhs] *)
Ltac rewrite_in_lhs x E :=
  lazymatch goal with |- @eq ?A ?lhs ?rhs =>
  let lhs_d := fresh "lhs_d" in
  pose (lhs_d := lhs);
  pattern x in (value of lhs_d);
  let lhs' := eval cbv delta [lhs_d] in lhs_d in
  lazymatch lhs' with ?f _ =>
  refine (f_equal f E)
  end end.

Ltac build_rewrite_ctx x E :=
  lazymatch goal with
  | |- rewrite_ctx nil _ _ =>
      exact RewCTX_Nil
  | |- rewrite_ctx (existT _ ?v ?sel :: ?c0) _ _ =>
      let Ev := fresh "Ev" in
      unshelve epose (Ev := _ : v = _);
        [ shelve | rewrite_in_lhs x E | ];
      let v' := type of Ev in
      match v' with _ = ?v' =>
      tryif constr_eq_strict v v'
      then refine (@RewCTX_Skip _ c0 _ _ _)
      else (
      tryif
        refine (@RewCTX_NDep (Vprop.ty v) (Vprop.sl v) (Vprop.sl v') _ sel c0 _ _ _);
        [cbn; rewrite E; reflexivity|]
      then  idtac
      else  refine (@RewCTX_Dep v v' Ev sel c0 _ _ _)
      )end;
      clear Ev;
      build_rewrite_ctx x E
  end.

Ltac build_Rewrite :=
  lazymatch goal with
  | |- Rewrite_Spec ?x _ _ _ _ =>
    simple refine (Rewrite_SpecI _ _ _);
    [ shelve | (* c1 *) intro; shelve
    | (* R *)
      let E := fresh "E" in intro E;
      build_rewrite_ctx x E
    | shelve | (* PRD *) Tac.cbn_refl
    | (* Ef *) Tac.cbn_refl ]
  end.

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
Section Change.
  Context [CT : CP.context] [A : Type] (P : A -> CTX.t * CTX.t).

  Inductive Change_Spec (ctx : CTX.t) (s : i_sig_t unit ctx) (f : i_spec_t s) : Prop
    := Change_SpecI
    (p : A)
    (IJ : InjPre_SFrame_Spec (fst (P p)) ctx {|
      sf_csm  := Sub.const (fst (P p)) true;
      sf_prd  := fun _ => VpropList.of_ctx (snd (P p));
    |} (FunProg.Bind (FunProg.Assert (SLprop.imp (CTX.sl (fst (P p))) (CTX.sl (snd (P p))))) (TF.of_fun (fun _ =>
        FunProg.Ret (TF.mk _ tt (VpropList.sel_of_ctx (snd (P p)))))))
    s f).
  
  Program Definition gChange : instr CT unit := {|
    i_impl := CP.Ret tt;
    i_spec := fun ctx => Change_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_SFrame IJ); clear IJ.
    do 2 intro; cbn in *.
    case PRE as (IMP & POST); cbn in POST.
    apply SP.CRet.
    EApply. Apply POST.
    rewrite TF.to_of_tu, VpropList.inst_of_ctx, CTX.sl_app.
    unfold Sub.neg, Sub.const; rewrite Vector.map_const, CTX.Sub.sub_const_false.
    SL.normalize; exact IMP.
  Qed.
End Change.

Local Ltac build_Change :=
  simple refine (Change_SpecI _ _ _ _ _ _);
  [ shelve
  | (* IJ *)
    cbn;
    (* [p : A] can be a tuple let-matched by [P] *)
    repeat lazymatch goal with |- InjPre_SFrame_Spec (fst ?x) _  _ _ _ _ =>
      Tac.build_matched_shape x; cbn
    end;
    Tac.build_InjPre_SFrame ].

Section GGet.
  Context [CT : CP.context] [A : Type] (v : Vprop.p A).

  Inductive GGet_Spec (ctx : CTX.t) (s : i_sig_t A ctx) (f : i_spec_t s) : Prop
    := GGet_SpecI
    (a : A)
    (IJ : InjPre_SFrame_Spec [CTX.mka (v, a)] ctx {|
      sf_csm := Vector.cons _ false _ (Vector.nil _) <: Sub.t [_];
      sf_prd := fun _ => nil;
    |} (FunProg.Ret (TF.mk0 _ a Tuple.tt)) s f).

  Program Definition gGet : instr CT A := {|
    i_impl := CP.Oracle A;
    i_spec := fun ctx => GGet_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_SFrame IJ); clear IJ.
    do 2 intro; cbn in *.
    apply SP.COracle with (x := a).
    Apply tt.
    Apply PRE.
    reflexivity.
  Qed.
End GGet.

Local Ltac build_GGet :=
  simple refine (GGet_SpecI _ _ _ _ _ _);
  [ shelve | Tac.build_InjPre_SFrame ].

Section Assert.
  Context [CT : CP.context] [A : Type] (P : A -> CTX.t * Prop).

  Inductive Assert_Spec (ctx : CTX.t) (s : i_sig_t unit ctx) (f : i_spec_t s) : Prop
    := Assert_SpecI
    (p : A)
    (IJ : InjPre_SFrame_Spec (fst (P p)) ctx {|
      sf_csm  := Sub.const (fst (P p)) false;
      sf_prd  := fun _ => nil;
    |} (FunProg.Bind (FunProg.Assert (snd (P p))) (TF.of_fun (fun _ =>
        FunProg.Ret (TF.mk0 _ tt Tuple.tt))))
    s f).
  
  Program Definition Assert : instr CT unit := {|
    i_impl := SP.sl_assert (SLprop.ex A (fun p =>
                SLprop.pure (snd (P p)) ** CTX.sl (fst (P p))))%slprop;
    i_spec := fun ctx => Assert_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_SFrame IJ); clear IJ.
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
  simple refine (Assert_SpecI _ _ _ _ _ _);
  [ shelve
  | (* IJ *)
    cbn;
    (* [p : A] can be a tuple let-matched by [P] *)
    repeat lazymatch goal with |- InjPre_SFrame_Spec (fst ?x) _  _ _ _ _ =>
      Tac.build_matched_shape x; cbn
    end;
    Tac.build_InjPre_SFrame ].


(* Lemmas for common vprops *)

Derive elim_empty_group_spec SuchThat (
  VLem SPEC (_ : unit)
  'v [] [vgroup [] ~> v] True
  '(_ : unit) tt [] True
  elim_empty_group_spec) As elim_empty_group.
Proof.
  init_lemma () () ?; reflexivity.
Qed.

Section Intro_True.
  Context {A : Type}.

Derive intro_true_spec SuchThat (
  VLem SPEC (v : Vprop.p A)
  'sel [] [v ~> sel] True
  '(_ : unit) tt [vtrue ~> tt] True
  intro_true_spec) As intro_true.
Proof.
  init_lemma ? ? ?; split.
Qed.
End Intro_True.


Module Tactics.
  #[export] Hint Extern 1 (Rewrite_Spec _ _ _ _ _) =>
    Tac.init_HasSpec_tac ltac:(fun _ => build_Rewrite) : HasSpecDB.
  #[export] Hint Extern 1 (Change_Spec _ _ _ _) =>
    Tac.init_HasSpec_tac ltac:(fun _ => build_Change)  : HasSpecDB.
  #[export] Hint Extern 1 (GGet_Spec      _ _ _ _) =>
    Tac.init_HasSpec_tac ltac:(fun _ => build_GGet)    : HasSpecDB.
  #[export] Hint Extern 1 (Assert_Spec    _ _ _ _) =>
    Tac.init_HasSpec_tac ltac:(fun _ => build_Assert)  : HasSpecDB.
End Tactics.
Export Tactics.
