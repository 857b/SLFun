From SLFun Require Import Util Values SL VProg.Vprop.
From SLFun Require ConcreteProg SLProg FunProg.
From Coq   Require Import Lists.List Setoids.Setoid.

Import SLNotations ListNotations.
Import SL.Tactics SLProg.Tactics.


Module Abbrev.
  Module CP  := SLFun.ConcreteProg.
  Module SP  := SLFun.SLProg.
  Module FP  := SLFun.FunProg.
  Module Sub := CTX.Sub.
End Abbrev.
Import Abbrev.

(* Type family *)
Module TF.
  Include DTuple.

  Definition mk_p (p_val : Type) (p_sel : p_val -> list Type) : p :=
    Pcons p_val (fun x => p_tu (p_sel x)).
  
  Definition mk_t (p_val : Type) (p_sel : p_val -> list Type) : Type :=
DTuple.t (mk_p p_val p_sel).

  Definition mk [p_val : Type] (p_sel : p_val -> list Type)
    (v_val : p_val) (v_sel : Tuple.t (p_sel v_val)) : mk_t p_val p_sel
    := pair v_val (of_tu v_sel).
  Global Arguments mk _ _ _ _/.

  Definition v_val [p_val p_sel] (v : t (mk_p p_val p_sel)) : p_val :=
    let '(existT _ x _) := v in x.

  Definition v_sel [p_val p_sel] (v : t (mk_p p_val p_sel)) : Tuple.t (p_sel (v_val v)) :=
    let '(existT _ _ s) := v in to_tu s.

  Lemma v_sel_mk [p_val p_sel] v s:
    v_sel (@mk p_val p_sel v s) = s.
  Proof. apply to_of_tu. Qed.
End TF.

Module Spec.
Section Spec.
  Local Set Implicit Arguments.
  Variables (GI : option Type) (A : Type) (GO : option (A -> Type)).

  Definition ghin_t : Type := OptTy.t GI.
  Definition ghout_t (x : A) : Type := OptTy.t (option_map (fun g => g x) GO).
  
  Definition opt_sigG : Type :=
    match GO with
    | Some GO => CP.sigG A GO
    | None    => A
    end.

  Definition to_opt_sigG : CP.sigG A ghout_t -> opt_sigG.
  Proof.
    unfold ghout_t, opt_sigG.
    case GO as [T|].
    - exact (fun x => x).
    - exact (fun '(CP.existG _ x _) => x).
  Defined.

  Definition of_opt_sigG : opt_sigG -> CP.sigG A ghout_t.
  Proof.
    unfold ghout_t, opt_sigG.
    case GO as [T|].
    - exact (fun x => x).
    - exact (fun x => CP.existG _ x tt).
  Defined.

  Lemma opt_sigG_iso : type_iso (CP.sigG A ghout_t) opt_sigG to_opt_sigG of_opt_sigG.
  Proof.
    unfold ghout_t, opt_sigG, to_opt_sigG, of_opt_sigG.
    case GO as [T|]; split; cbn; try reflexivity.
    intros [? []]; reflexivity.
  Qed.


  Record t_r3 (vp : VpropList.t) : Type := mk_r3 {
    spost : VpropList.sel_t vp; (* post condition selectors *)
    ens   : Prop;               (* ensures *)
  }.

  Record t_r2 (req : Prop) : Type := mk_r2 {
    sel1_t : list Type;
    vpost  : VpropList.t; (* post condition vprops *)
    f_r3 : Tuple.arrow sel1_t (fun _ => req -> t_r3 vpost);
  }.
  Global Arguments mk_r2 [req] _ _ _.
  Definition f_r3_f (req : Prop) (s : t_r2 req):
    forall (sel1 : Tuple.t (sel1_t s)) (REQ : req), t_r3 (vpost s) :=
    Tuple.to_fun (f_r3 s).
  Coercion f_r3_f : t_r2 >-> Funclass.

  Record t_r1 : Type := mk_r1 {
    prs : CTX.t; (* preserved *)
    pre : CTX.t; (* pre condition *)
    req : Prop;  (* requires *)
    f_r2 :> opt_sigG -> t_r2 req;
  }.
  Global Arguments mk_r1 : clear implicits.

  Record t_r0 : Type := mk_r0 {
    sel0_t : Type;
    f_r1 :> sel0_t -> t_r1;
  }.

  Definition t : Type := ghin_t -> t_r0.

  Definition post (vp : VpropList.t) (s : t_r3 vp) : CTX.t :=
    VpropList.inst vp (spost s).

End Spec.
Module Expanded. Section Expanded.
  Local Set Implicit Arguments.
  Variables (GI : option Type) (A : Type) (GO : option (A -> Type)).

  Record t_r3 : Type := mk_r3 {
    post : CTX.t;
    ens  : Prop;
  }.

  Record t_r2 (req : Prop) : Type := mk_r2 {
    sel1_t : Type;
    f_r3 :> sel1_t -> req -> t_r3;
  }.

  Record t_r1 : Type := mk_r1 {
    prs : CTX.t;
    pre : CTX.t;
    req : Prop;
    f_r2 :> opt_sigG GO -> t_r2 req;
  }.
  Global Arguments mk_r1 : clear implicits.

  Record t_r0 : Type := mk_r0 {
    sel0_t : Type;
    f_r1 :> sel0_t -> t_r1;
  }.

  Definition t : Type := ghin_t GI -> t_r0.


  Definition tr_post [req] (e : Expanded.t_r2 req) (REQ : req) : SLprop.t :=
    SLprop.ex (sel1_t e) (fun sel1 =>
      SLprop.pure (ens (e sel1 REQ)) **
      CTX.sl (post (e sel1 REQ)))%slprop.

  Definition tr_1
    [B] (PT : (opt_sigG GO -> SLprop.t) -> B -> SLprop.t)
    (vs : Expanded.t_r1) (REQ : req vs) : SP.Spec.t B :=
    {|
      SP.Spec.pre  :=
        CTX.sl (pre vs) **
        CTX.sl (prs vs);
      SP.Spec.post := PT (fun xG =>
        tr_post (vs xG) REQ **
        CTX.sl (prs vs));
    |}%slprop.

  Definition tr (vs : t) (ss : SP.Spec.t A) : Prop :=
    exists (gi : ghin_t GI) (sel0 : sel0_t (vs gi)) (REQ : req (vs gi sel0)),
    SP.Spec.eq ss
      (tr_1 (fun pt x => SLprop.ex (ghout_t GO x) (fun go => pt (to_opt_sigG (CP.existG _ x go))))
            (vs gi sel0) REQ).


  Definition to_expanded2 [req] (s : Spec.t_r2 req) : Expanded.t_r2 req :=
    @mk_r2 req (Tuple.t (Spec.sel1_t s)) (fun sel1 REQ =>
    mk_r3 (Spec.post (s sel1 REQ)) (Spec.ens (s sel1 REQ))).

  Definition to_expanded (s : Spec.t GI GO) : Expanded.t :=
    fun gi =>
    @mk_r0 (Spec.sel0_t (s gi)) (fun sel0 =>
    mk_r1 (Spec.prs (s gi sel0)) (Spec.pre (s gi sel0)) (Spec.req (s gi sel0)) (fun xG =>
    to_expanded2 (s gi sel0 xG))).

  Inductive of_expanded3 (e : Expanded.t_r3) : Spec.t_r3 (VpropList.of_ctx (post e)) -> Prop
    := of_expanded3I:
    of_expanded3 e (Spec.mk_r3 _ (VpropList.sel_of_ctx (post e)) (ens e)).

  Inductive of_expanded2 [req] (e : Expanded.t_r2 req) : Spec.t_r2 req -> Prop
    := of_expanded2I
    (* changing [sel1_t] into a tuple *)
    (sel1_tu   : list Type)
    (sel1_tu_f : sel1_t e -> Tuple.t sel1_tu)
    (sel1_tu_g : Tuple.t sel1_tu -> sel1_t e)
    (sel1_TU   : Tuple.type_iso_tu (sel1_t e) sel1_tu sel1_tu_f sel1_tu_g)
    (sel1_TU_GOAL : forall sel1 : sel1_t e,
      Tuple.type_iso_tu_goal (e sel1) _ sel1_TU)
    (* the vprops of [post] must be independents of [sel1] *)
    (vpost : VpropList.t)
    (VPOST : Tuple.arrow sel1_tu (fun sel1' =>
      let sel1 : sel1_t e := sel1_tu_g sel1' in
      forall REQ : req,
      VpropList.of_ctx (post (e sel1 REQ)) = vpost))
    (s3 : Tuple.arrow sel1_tu (fun _ => req -> Spec.t_r3 vpost))
    (S3 : Tuple.arrow sel1_tu (fun sel1' =>
      let sel1 : sel1_t e := sel1_tu_g sel1' in
      forall REQ : req,
      of_expanded3 (e sel1 REQ)
        (eq_rect_r Spec.t_r3 (Tuple.to_fun s3 sel1' REQ)
                   (Tuple.to_fun VPOST sel1' REQ)))):
    of_expanded2 e (@Spec.mk_r2 req sel1_tu vpost s3).

  Inductive of_expanded1 (e : Expanded.t_r1) : Spec.t_r1 GO -> Prop
    := of_expanded1I
    (s2 : opt_sigG GO -> Spec.t_r2 (req e))
    (S2 : forall (xG : opt_sigG GO), of_expanded2 (e xG) (s2 xG)):
    of_expanded1 e (@Spec.mk_r1 A GO (prs e) (pre e) (req e) s2).

  Inductive of_expanded0 (e : Expanded.t_r0) : Spec.t_r0 GO -> Prop
    := of_expanded0I
    (s1 : sel0_t e -> Spec.t_r1 GO)
    (S1 : forall sel0 : sel0_t e, of_expanded1 (e sel0) (s1 sel0)):
    of_expanded0 e (@Spec.mk_r0 A GO (sel0_t e) s1).

  Definition of_expanded (e : Expanded.t) (s : Spec.t GI GO) : Prop :=
    forall gi : ghin_t GI, of_expanded0 (e gi) (s gi).

  Lemma of_expanded2_equiv [req] e s REQ
    (E : @of_expanded2 req e s):
    SLprop.eq (tr_post e REQ) (tr_post (to_expanded2 s) REQ).
  Proof.
    destruct E; unfold tr_post, to_expanded2; cbn.
    eenough (forall sel1' : Tuple.t sel1_tu, SLprop.eq _ _) as C.
    - apply SLprop.eq_iff_imp; split; cycle 1.
      + Intro sel1'.
        Apply (sel1_tu_g sel1').
        rewrite (C sel1'). reflexivity.
      + Intro sel1.
        Apply (sel1_tu_f sel1).
        rewrite C, (proj1 sel1_TU). reflexivity.
    - intro sel1'.
      apply R_refl. reflexivity.
      set (x_S3 := Tuple.to_fun S3 sel1' REQ); clearbody x_S3; clear S3.
      set (x_s3 := Tuple.to_fun s3 sel1' REQ) in *.
        simpl in x_s3, x_S3; fold x_s3 in x_S3; clearbody x_s3; clear s3.
      set (x_VPOST := Tuple.to_fun VPOST sel1' REQ) in *; clearbody x_VPOST; clear VPOST.
      destruct x_VPOST; cbn in *.
      case x_S3; cbn.
      rewrite VpropList.inst_of_ctx.
      reflexivity.
  Qed.

  Lemma of_expanded_equiv e s ss
    (E : of_expanded e s):
    tr e ss <-> tr (to_expanded s) ss.
  Proof.
    unfold tr, tr_1; cbn.
    apply Morphisms_Prop.ex_iff_morphism; intro gi.
    case (E gi) as [s1 S1]; cbn.
    apply Morphisms_Prop.ex_iff_morphism; intro sel0.
    case (S1 sel0) as [s2 S2]; cbn.
    setoid_rewrite (fun REQ xG => of_expanded2_equiv REQ (S2 xG)).
    reflexivity.
  Qed.
End Expanded. End Expanded.
  Global Arguments t          : clear implicits.
  Global Arguments mk_r1 [A] [GO].
  Global Arguments Expanded.t : clear implicits.
  Global Arguments Expanded.mk_r1 [A] [GO].
  
  Definition tr [GI A GO] (s : t GI A GO) : SP.Spec.t A -> Prop :=
      Expanded.tr (Expanded.to_expanded s).
  
  Definition spec_match [GI A GO] (vs : t GI A GO) (ss : SP.Spec.t A -> Prop) : Prop :=
    forall s0, tr vs s0 ->
    exists s1, SP.Spec.le s1 s0 /\ ss s1.
End Spec.

Section F_SPEC.
  Local Set Implicit Arguments.
  Variable sg : f_sig.

  Record f_sigh := mk_f_sigh {
    f_ghin_t  : option (f_arg_t sg -> Type);
    f_ghout_t : option (f_ret_t sg -> Type);
  }.
  Variable sgh : f_sigh.

  Definition f_ghin_t_x (x : f_arg_t sg) : option Type :=
    option_map (fun gi => gi x) (f_ghin_t sgh).

  Definition sigh_spec_t (x : f_arg_t sg) :=
    Spec.t (f_ghin_t_x x) (f_ret_t sg) (f_ghout_t sgh).

  Definition f_spec :=
    forall x, sigh_spec_t x.
  
  Definition f_spec_exp :=
    forall (x : f_arg_t sg), Spec.Expanded.t (f_ghin_t_x x) (f_ret_t sg) (f_ghout_t sgh).

  Definition match_f_spec (vs : f_spec) (ss : SP.f_spec sg) : Prop :=
    forall x, Spec.spec_match (vs x) (ss x).

  Definition tr_f_spec (vs : f_spec) : SP.f_spec sg :=
    fun x => Spec.tr (vs x).

  Lemma tr_f_spec_match (s : f_spec):
    match_f_spec s (tr_f_spec s).
  Proof.
    intros x s0 TR; do 2 esplit.
    - reflexivity.
    - exact TR.
  Qed.

  Definition cp_f_spec (s : f_spec) : CP.f_spec sg :=
    SP.tr_f_spec (tr_f_spec s).

  Record FSpec (e : f_spec_exp) := mk_FSpec {
    m_spec  : f_spec;
    m_equiv : forall x : f_arg_t sg, Spec.Expanded.of_expanded (e x) (m_spec x);
  }.

  Variable (CT : CP.context).
  Let SIG : sig_context         := projT1 CT.
  Let SPC : CP.spec_context SIG := projT2 CT.

  Definition fun_has_spec (f : fid) (HSIG : SIG f = Some sg)
      (x : f_arg_t sg) (s : sigh_spec_t x) : Prop :=
    Spec.spec_match s (SP.fun_has_spec SPC f x HSIG).
  
  Lemma cp_has_spec (f : fid)
    (HSIG : SIG f = Some sg)
    [s : f_spec] (HSPC : CP.fun_has_spec SPC f HSIG = cp_f_spec s):
    forall x, fun_has_spec f HSIG (s x).
  Proof.
    intros x ss TR.
    do 2 esplit. reflexivity.
    unfold SP.fun_has_spec; rewrite HSPC.
    apply (SP.tr_f_spec_match _), TR.
  Qed.
  
  Record f_declared (f : fid) (s : f_spec) : Prop := {
    fd_Hsig  : SIG f = Some sg;
    fd_Hspec : forall x, fun_has_spec f fd_Hsig (s x);
  }.

  Lemma cp_is_declared (f : fid) (s : f_spec)
    (HSIG : SIG f = Some sg)
    (HSPC : CP.fun_has_spec SPC f HSIG = cp_f_spec s):
    f_declared f s.
  Proof.
    exists HSIG.
    apply cp_has_spec, HSPC.
  Defined.

  Record f_decl (s : f_spec) : Type := {
    fd_id : fid;
    fd_H  : f_declared fd_id s;
  }.
End F_SPEC.
Global Arguments FSpec [sg] sgh e.

Definition mk_f_sig1 (arg_t : Type) (ghin_t  : option (arg_t -> Type))
                    (ret_t : Type) (ghout_t : option (ret_t -> Type))
  : f_sigh (mk_f_sig arg_t ret_t)
  := mk_f_sigh (mk_f_sig arg_t ret_t) ghin_t ghout_t.


Section GhostLemma.
  Import Spec.
  Local Set Implicit Arguments.
  Variable (sg : f_sig).
  Definition lem_sigh : f_sigh sg := mk_f_sigh _ None None.

  Definition ghost_spec := f_spec lem_sigh.
  
  Definition ghost_lem (s : ghost_spec) : Prop :=
    forall (x    : f_arg_t    sg), let s  := s x tt in
    forall (sel0 : Spec.sel0_t s), let s0 := s sel0 in
    forall REQ : Spec.req s0,
    SLprop.imp
      (CTX.sl (Spec.pre s0 ++ Spec.prs s0))
      (SLprop.ex (f_ret_t sg) (fun res => let s := s0 res  in
       SLprop.ex (Tuple.t (Spec.sel1_t s)) (fun sel1 => let s := s sel1 REQ in
       SLprop.pure (Spec.ens s) **
       CTX.sl (Spec.post s ++ Spec.prs s0))))%slprop.
End GhostLemma.

Section VProg.

(* [i_spec_t] *)

Local Set Implicit Arguments.
Record i_spec_t (A : Type) (ctx : CTX.t) := mk_i_spec {
  sf_csm  : Sub.t ctx;
  sf_prd  : A -> VpropList.t;
  sf_spec : FP.instr (TF.mk_p A (fun x => VpropList.sel (sf_prd x)));
}.
Local Unset Implicit Arguments.

Section GETTERS.
  Context [A ctx] (s : i_spec_t A ctx).

  Definition sf_rsel (x : A) : list Type :=
    VpropList.sel (sf_prd s x).

  Definition sf_rvar : TF.p :=
    TF.mk_p A sf_rsel.
  
  Definition sf_rvar_t : Type :=
    TF.t sf_rvar.

  Definition sf_prd_ctx (r : sf_rvar_t) : CTX.t :=
    VpropList.inst (sf_prd s (TF.v_val r)) (TF.v_sel r).

  Definition sf_post_ctx (r : sf_rvar_t) : CTX.t :=
    sf_prd_ctx r ++ CTX.sub ctx (Sub.neg (sf_csm s)).

  Definition sf_post (post : sf_rvar_t -> Prop) (x : A) : SLprop.t :=
    SLprop.ex (VpropList.sel_t (sf_prd s x)) (fun sels =>
      let r := TF.mk sf_rsel x sels in
      SLprop.pure (post r) **
      CTX.sl (sf_post_ctx r))%slprop.
End GETTERS.
Global Arguments sf_rsel _ _ !_/.
Global Arguments sf_rvar _ _ !_/.
Global Arguments sf_rvar_t _ _ !_/.
Global Arguments sf_prd_ctx _ _ !_ !_/.
Global Arguments sf_post_ctx _ _ !_ !_/.
Global Arguments sf_post _ _ !_ _/.

(* [instr] *)

  Context (CT : CP.context).
  Let SIG : sig_context         := projT1 CT.
  Let SPC : CP.spec_context SIG := projT2 CT.

Definition sound_spec [A : Type] (i : @CP.instr SIG A) (ctx : CTX.t) (s : i_spec_t A ctx) : Prop :=
  forall (post : sf_rvar_t s -> Prop)
         (PRE : FP.wlp (sf_spec s) post),
  SP.sls SPC i {|
    SP.Spec.pre  := CTX.sl ctx;
    SP.Spec.post := sf_post s post;
  |}.

Definition i_spec_p [A : Type] (i : @CP.instr SIG A) (ctx : CTX.t) : Type :=
  { sp : i_spec_t A ctx -> Prop | forall s (SP : sp s), sound_spec i ctx s }.

Local Set Implicit Arguments.
Record instr (A : Type) := mk_instr {
  i_impl : @CP.instr SIG A;
  i_spec : forall ctx : CTX.t, i_spec_p i_impl ctx;
}.
Local Unset Implicit Arguments.

Inductive HasSpec [A : Type] (i : instr A) (ctx : CTX.t) (s : i_spec_t A ctx) : Prop :=
  HasSpecI (S : sound_spec (i_impl i) ctx s).

Lemma HasSpec_ct [A i ctx s]
  (C : proj1_sig (i_spec i ctx) s):
  @HasSpec A i ctx s.
Proof.
  constructor; apply (proj2_sig (i_spec i ctx) s), C.
Qed.

(* Transformation *)

Definition TrSpecH [A : Type] [ctx0 ctx1 : CTX.t] (s0 : i_spec_t A ctx0) (s1 : i_spec_t A ctx1) : Prop :=
  forall (i : @CP.instr SIG A) (S0 : sound_spec i ctx0 s0), sound_spec i ctx1 s1.

Inductive TrSpec [A : Type] [ctx : CTX.t] (s0 s1 : i_spec_t A ctx) : Prop :=
  TrSpecI (T : TrSpecH s0 s1).

Global Instance TrSpec_PreOrder A ctx : PreOrder (@TrSpec A ctx).
Proof.
  split.
  - constructor; unfold TrSpecH; auto.
  - intros ? ? ? [] []; constructor; unfold TrSpecH in *; auto.
Qed.

Lemma transform_spec [A ctx i s0 s1]
  (H : HasSpec i ctx s0)
  (T : TrSpec s0 s1):
  @HasSpec A i ctx s1.
Proof.
  constructor; apply T, H.
Qed.

Section AddCsm.
  Context [A : Type] [ctx : CTX.t] (s : i_spec_t A ctx) (csm : Sub.t ctx).
  
  Let acsm := CTX.sub ctx (Sub.minus csm (sf_csm s)).

  Definition add_csm : i_spec_t A ctx
    :=
    {|
      sf_csm  := Sub.or (sf_csm s) csm;
      sf_prd  := fun x => sf_prd s x ++ VpropList.of_ctx acsm;
      sf_spec := FP.Bind (sf_spec s) (TF.of_fun (T:=sf_rvar s) (fun x =>
                   FP.Ret (TF.mk _ (TF.v_val x) (VpropList.app_sel (TF.v_sel x) (VpropList.sel_of_ctx acsm)))
                 ))
    |}.

  Local Opaque TF.to_fun TF.of_fun.

  Lemma Tr_add_csm:
    TrSpec s add_csm.
  Proof.
    constructor.
    intros i S0 post PRE; simpl in PRE.
    simpl in PRE.
    eapply SP.Cons.
      { apply S0, PRE. }
    clear S0 PRE.
    split; simpl. reflexivity.
    intro x; unfold add_csm, sf_post, sf_post_ctx, sf_prd_ctx, sf_rsel; cbn.
    Intro sel0.
    Apply (VpropList.app_sel sel0 (VpropList.sel_of_ctx acsm)).
    rewrite TF.to_of_fun; cbn.
    rewrite !TF.to_of_tu.
    apply SLprop.star_morph_imp. reflexivity.
    rewrite VpropList.inst_app, !CTX.sl_app; SL.normalize.
    apply SLprop.star_morph_imp. reflexivity.
    unfold acsm; rewrite VpropList.inst_of_ctx.
    set (c0 := CTX.sub ctx (Sub.neg (sf_csm s))).
    rewrite (CTX.sl_split c0 (Sub.push (Sub.neg (sf_csm s)) csm)).
    unfold Sub.neg, CTX.sub, c0; rewrite <- Sub.push_map with (f := negb).
    rewrite !Sub.sub_push.
    apply R_refl. reflexivity.
    do 3 f_equal; apply Vector.ext; intro k;
      unfold Sub.and, Sub.or, Sub.minus;
      repeat progress (erewrite ?Vector.nth_map2, ?Vector.nth_map by reflexivity).
    - apply Bool.andb_comm.
    - symmetry; apply Bool.negb_orb.
  Qed.
End AddCsm.
Global Arguments add_csm _ _ !_ !_/.

Section ChangePrd.
  Context [A : Type] [ctx : CTX.t] (s : i_spec_t A ctx)
          (prd : A -> VpropList.t)
          (rsel : forall r : sf_rvar_t s, VpropList.sel_t (prd (TF.v_val r)))
          (RSEL : forall r : sf_rvar_t s,
                  CTX.Inj.beq (VpropList.inst (prd (TF.v_val r)) (rsel r))
                              (sf_prd_ctx s r)).
  Definition change_prd : i_spec_t A ctx
    :=
    {|
      sf_csm  := sf_csm s;
      sf_prd  := prd;
      sf_spec := FP.Bind (sf_spec s) (TF.of_fun (T:=sf_rvar s) (fun r =>
                   FP.Ret (TF.mk _ (TF.v_val r) (rsel r))
                 ))
    |}.

  Local Opaque TF.to_fun TF.of_fun.

  Lemma Tr_change_prd:
    TrSpec s change_prd.
  Proof.
    constructor.
    intros i S post PRE.
    eapply SP.Cons.
      { apply S, PRE. }
    clear S PRE.
    split. reflexivity.
    unfold sf_post, sf_post_ctx; cbn.
    intro x.
    Intro sel.
    Apply (rsel (TF.mk _ x sel)).
    rewrite TF.to_of_fun.
    cbn; rewrite !CTX.sl_app.
    rewrite (CTX.Inj.beqE (RSEL (TF.mk _ x sel))), !TF.to_of_tu.
    reflexivity.
  Qed.
End ChangePrd.
Global Arguments change_prd _ _ !_ _ _/.

Lemma Tr_change_exact [A ctx s s1 csm1 prd1] [f1 : FP.instr (TF.mk_p A (fun x => VpropList.sel (prd1 x)))]
  (CSM  : csm1 = Sub.or (sf_csm s) csm1)
  (S1   : s1 = add_csm s csm1)
  (rsel : TF.arrow (sf_rvar s1) (fun r => VpropList.sel_t (prd1 (TF.v_val r))))
  (RSEL : TF.arrow (sf_rvar s1) (fun r =>
          CTX.Inj.beq (VpropList.inst (prd1 (TF.v_val r)) (TF.to_fun rsel r))
                      (sf_prd_ctx s1 r)))
  (F1   : f1 = sf_spec (change_prd s1 prd1 (TF.to_fun rsel))):
  @TrSpec A ctx s (mk_i_spec csm1 prd1 f1).
Proof.
  transitivity s1.
  - rewrite S1.
    apply Tr_add_csm.
  - replace csm1 with (sf_csm s1)
      by (rewrite CSM, S1; reflexivity).
    rewrite F1.
    apply Tr_change_prd, (TF.to_fun RSEL).
Qed.

Section AddFrame.
  Context [A : Type] [ctx : CTX.t] (s : i_spec_t A ctx) (frame : CTX.t).

  Definition add_frame : i_spec_t A (ctx ++ frame) := {|
    sf_csm  := Sub.app (sf_csm s) (Sub.const frame false);
    sf_prd  := sf_prd s;
    sf_spec := sf_spec s
  |}.

  Lemma Tr_add_frame:
    TrSpecH s add_frame.
  Proof.
    intros i S0 post WLP.
    eapply SP.CFrame with (fr := CTX.sl frame).
      { apply S0, WLP. }
    split; unfold sf_post, sf_post_ctx; cbn.
    - rewrite CTX.sl_app; reflexivity.
    - intro x; SL.normalize.
      Intro sel. Intro POST.
      Apply sel. Apply POST.
      unfold Sub.neg, Sub.const.
      rewrite Sub.map_app, Sub.sub_app, Vector.map_const, Sub.sub_const_true, !CTX.sl_app.
      SL.normalize. reflexivity.
  Qed.

End AddFrame.

Section InjPre.
  Context (m : CTX.t) (ctx : CTX.t).

  Section Full.
    Context (add : CTX.t) [A] (F : i_spec_t A (m ++ add)) (F' : i_spec_t A ctx).

    Inductive InjPre_Spec : Prop
      := InjPre_SpecI
      (rev_f : Sub.t (m ++ add) -> (Sub.t ctx * CTX.t))
      (ij : CTX.Inj.itrf m ctx add rev_f)
      (E  : F' =
        let (ncsm, rem) := rev_f (Sub.neg (sf_csm F)) in
        {|
          sf_csm  := Sub.neg ncsm;
          sf_prd  := fun x : A => sf_prd F x ++ VpropList.of_ctx rem;
          sf_spec := FP.Bind (sf_spec F) (TF.of_fun (T := sf_rvar F) (fun r =>
                     FP.Ret (TF.mk _ (TF.v_val r) (VpropList.app_sel (TF.v_sel r) (VpropList.sel_of_ctx rem)))))
        |}).

    Local Opaque DTuple.to_fun.
    Local Set Implicit Arguments.

    Lemma Tr_InjPre (SP : InjPre_Spec):
      TrSpecH F F'.
    Proof.
      case SP as [rev_f [FWD BWD] E].
      specialize (BWD (Sub.neg (sf_csm F)));
        destruct rev_f as (ncsm, rem) in BWD, E;
        cbn in BWD; subst F'.
      intros i S0 post WLP; cbn in post, WLP.
      eapply SP.Cons.
        { apply S0, WLP. }
      clear WLP.
      split; unfold sf_post, sf_post_ctx; cbn.
      - exact FWD.
      - intro x.
        Intro sel; cbn.
        rewrite TF.to_of_fun; cbn.
        rewrite TF.to_of_tu;  cbn.
        Intro POST.
        EApply. Apply POST.
        unfold sf_prd_ctx; cbn.
        rewrite !TF.to_of_tu, VpropList.inst_app, VpropList.inst_of_ctx, !CTX.sl_app.
        SL.normalize.
        apply SLprop.star_morph_imp. reflexivity.
        rewrite BWD, SLprop.star_comm.
        apply Util.R_refl. reflexivity. do 3 f_equal.
        unfold Sub.neg.
        rewrite Vector.map_map, <- Vector.map_id at 1.
        apply Vector.map_ext.
        intros []; reflexivity.
    Qed.
  End Full.
  Section Frame.
    Context [A] (F : i_spec_t A m) (F' : i_spec_t A ctx).

    Inductive InjPre_Frame_Spec : Prop
      := InjPre_Frame_SpecI
      (frame : CTX.t)
      (ij : InjPre_Spec frame (add_frame F frame) F').

    Local Set Implicit Arguments.

    Lemma Tr_InjPre_Frame (SP : InjPre_Frame_Spec):
      TrSpecH F F'.
    Proof.
      case SP as [frame ij].
      intros i S0.
      eapply (Tr_InjPre ij), Tr_add_frame, S0.
    Qed.
  End Frame.
End InjPre.

(* Function definition *)

Section FunImpl.
  Context [GI : option Type] [A : Type] [GO : option (A -> Type)].
  Let AG := Spec.opt_sigG GO.

  Definition f_body1 : Type :=
    OptTy.arrow GI (fun gi => instr AG).

  Variables (body : f_body1) (spec : Spec.t GI A GO).
  Import Spec.

  Definition impl_match :=
    forall (gi : ghin_t GI) (sel0 : sel0_t (spec gi)) (REQ : req (spec gi sel0)),
    SP.sls SPC (i_impl (OptTy.to_fun' body gi))
      (Spec.Expanded.tr_1
        (fun pt xG => pt xG)
        (Spec.Expanded.f_r1 (Spec.Expanded.to_expanded spec gi) sel0)
        REQ).

  Lemma intro_impl_match
    (H : forall (gi : ghin_t GI) (sel0 : Spec.sel0_t (spec gi)) (REQ : Spec.req (spec gi sel0)),
         let ctx : CTX.t := Spec.pre (spec gi sel0) ++ Spec.prs (spec gi sel0) in
         exists f : i_spec_t AG ctx,
         sf_csm f = Sub.const ctx true /\
         sound_spec (i_impl (OptTy.to_fun' body gi)) ctx f /\
         FP.wlp (sf_spec f) (fun r =>
           let xG     := TF.v_val r in
           let f_post := VpropList.inst (sf_prd f (TF.v_val r)) (TF.v_sel r) in
           exists sel1 : Tuple.t (Spec.sel1_t (spec gi sel0 xG)),
           CTX.Inj.beq (Spec.post (spec gi sel0 xG sel1 REQ) ++ Spec.prs (spec gi sel0)) f_post /\
           Spec.ens (spec gi sel0 xG sel1 REQ)
         )):
    impl_match.
  Proof.
    intros gi sel0 REQ.
    unfold Expanded.tr_1; cbn.
    case (H gi sel0 REQ) as (f & F_CSM & F_SPEC & WLP); clear H.
    eapply SP.Cons.
      { apply F_SPEC, WLP. }
    clear F_SPEC WLP.
    unfold sf_post, sf_post_ctx; split; cbn.
    - rewrite CTX.sl_app; reflexivity.
    - intro xG.
      Intro rsel.
      Intro (sel1 & ij & ENS).
      unfold Expanded.tr_post; cbn; SL.normalize.
      Apply sel1.
      Apply ENS.
      rewrite F_CSM; unfold Sub.neg, Sub.const;
        rewrite Vector.map_const, Sub.sub_const_false, app_nil_r.
      apply CTX.Inj.beqE in ij; rewrite CTX.sl_app in ij.
      rewrite ij; reflexivity.
  Qed.

  Section Impl_Match.
    Variables (body_1 : instr AG) (s_1 : Spec.t_r1 GO).

  Let s_post (xG : AG) (sel1 : Tuple.t (Spec.sel1_t (s_1 xG))) (REQ : Spec.req s_1) :=
    Spec.post (s_1 xG sel1 REQ) ++ Spec.prs s_1.
  Let s_vpost (xG : AG) :=
    Spec.vpost (s_1 xG) ++ VpropList.of_ctx (Spec.prs s_1).
  Let rvar :=
    TF.mk_p AG (fun xG => VpropList.sel (s_vpost xG)).

  Local Lemma s_vpost_eq (xG : AG) (sel1 : Tuple.t (Spec.sel1_t (s_1 xG))) (REQ : Spec.req s_1):
    VpropList.of_ctx (s_post xG sel1 REQ) = s_vpost xG.
  Proof.
    unfold s_post, s_vpost, post.
    rewrite VpropList.app_of_ctx, VpropList.of_inst.
    reflexivity.
  Defined.

  Inductive Impl_Match : Prop :=
    Impl_MatchI:
      let ctx : CTX.t := Spec.pre s_1 ++ Spec.prs s_1 in
      forall
      (* functional representation of the implementation *)
      (f : FP.instr rvar)
      (F : HasSpec body_1 ctx (mk_i_spec (Sub.const ctx true) s_vpost f))
      (* simplification of the existential quantification on sel1.
         Maybe we could expend the wlp of add_csm to remove the equalities on
         non consumed vprops ? *)
      (ex_sel1 : forall (x : AG) (REQ : Spec.req s_1) (P : Tuple.t (Spec.sel1_t (s_1 x)) -> Prop),
              Tuple.arrow (VpropList.sel (s_vpost x)) (fun _ => Prop))
      (EX_SEL1 : forall (x : AG) (REQ : Spec.req s_1) (P : Tuple.t (Spec.sel1_t (s_1 x)) -> Prop),
              Tuple.arrow (VpropList.sel (s_vpost x)) (fun rsel =>
              Tuple.ex (sel1_t (s_1 x)) (fun sel1 =>
              Tuple.typed_eq (VpropList.sel_of_ctx (s_post x sel1 REQ))
                             (eq_rect_r VpropList.sel_t rsel (s_vpost_eq x sel1 REQ)) /\
              P sel1) <-> Tuple.to_fun (ex_sel1 x REQ P) rsel))
      (* VC *)
      (WLP : forall REQ : Spec.req s_1,
             FP.wlpA f (TF.of_fun (T := rvar) (fun r =>
               let x := TF.v_val r in
               Tuple.to_fun (ex_sel1 x REQ (fun sel1 => Spec.ens (s_1 x sel1 REQ))) (TF.v_sel r)))),
      Impl_Match.
  End Impl_Match.

  Lemma intro_impl_match1
    (H : forall gi sel0, Impl_Match (OptTy.to_fun' body gi) (spec gi sel0)):
    impl_match.
  Proof.
    apply intro_impl_match.
    intros gi sel0 REQ ctx.
    destruct (H gi sel0); clear H.
    eexists. split. 2:split.
      2:apply F.
    - reflexivity.
    - clear F.
      eapply FP.wlp_monotone, WLP.
      intro r; rewrite TF.to_of_fun.
      clear WLP; simpl.
      intros (sel1 & [SEQ] & ENS)%(proj2 (Tuple.to_fun (EX_SEL1 _ REQ _) _))%Tuple.ex_iff.
      clear ex_sel1 EX_SEL1.
      exists sel1.
      split. 2:exact ENS.
      destruct r as [x sel]; cbn in *.
      set (x_VPOST := s_vpost_eq _ _ _) in SEQ; clearbody x_VPOST.
      destruct x_VPOST; cbn in *; rewrite <- SEQ.
      rewrite VpropList.inst_of_ctx.
      apply CTX.Inj.beq_iff.
      reflexivity.
  Qed.
End FunImpl.

Section FunImplBody.
  Local Set Implicit Arguments.
  Variables (sg : f_sig) (sgh : f_sigh sg).

  Definition f_body : Type :=
    forall (x : f_arg_t sg), @f_body1 (f_ghin_t_x sgh x) (f_ret_t sg) (f_ghout_t sgh).

  Variables (impl : f_body).

  Definition f_body_match (spec : f_spec sgh) : Prop :=
    forall x : f_arg_t sg, impl_match (impl x) (spec x).

  Definition f_ebody : @CP.f_impl SIG sg.
  Proof.
    assert (prj : Spec.opt_sigG (f_ghout_t sgh) -> @CP.instr SIG (f_ret_t sg)). {
      intro x; apply CP.Ret; revert x.
      case f_ghout_t as [GO|].
      - exact (fun '(CP.existG _ x _) => x).
      - exact (fun x => x).
    }
    intros arg.
    generalize (impl arg); clear impl.
    unfold f_ghin_t_x.
    case f_ghin_t as [GI|]; intro impl.
    - exact (CP.Bind (CP.Oracle (GI arg)) (fun gi => CP.Bind (i_impl (impl gi)) prj)).
    - exact (CP.Bind (i_impl impl) prj).
  Defined.

  Variable (spec : f_spec sgh).
  Hypothesis (M : f_body_match spec).

  Lemma f_ebody_tr:
    match_f_spec spec (fun x => SP.sls SPC (f_ebody x)).
  Proof.
    intros arg s (gi & sel0 & REQ & S).
    do 2 esplit. { setoid_rewrite S; reflexivity. }
    clear S.
    cbv delta [f_ebody].
    set (prj := fun x => CP.Ret _).
    eenough _ as PRJ. clearbody prj.
    unfold Spec.Expanded.tr_1; cbn.
    - unfold f_body, f_body_match, impl_match, f_spec, sigh_spec_t, f_ghin_t_x in *.
      destruct f_ghin_t; cbn in *.
      + eapply SP.Bind.
        { apply SP.Oracle with (x := gi). }
        intro; apply SP.PureE; intros ->.
        eapply SP.Bind.
        { apply M. }
        cbn. exact PRJ.
      + destruct gi.
        eapply SP.Bind.
        { exact (@M arg tt sel0 REQ). }
        exact PRJ.
    - subst prj; clear.
      unfold f_spec, sigh_spec_t in *.
      destruct f_ghout_t; cbn in *.
      + intros [res go].
        apply SP.CRet.
        Apply go.
        reflexivity.
      + intro res.
        apply SP.CRet.
        Apply tt.
        reflexivity.
  Qed.

  Lemma f_ebody_match_spec:
    CP.f_match_spec SPC f_ebody (cp_f_spec spec).
  Proof.
    intro arg.
    apply SP.wp_impl_tr_f_spec.
    intros s TR.
    apply f_ebody_tr in TR as (s' & LE & SLS).
    eapply SP.Cons; eassumption.
  Qed.

  Definition f_extract : Type :=
    { i : @CP.f_impl SIG sg | forall x : f_arg_t sg, CP.extract (f_ebody x) (i x) }.

  Variable (i : f_extract).

  Lemma f_extract_match_spec:
    CP.f_match_spec SPC (proj1_sig i) (cp_f_spec spec).
  Proof.
    intros arg s S m0 PRE.
    apply (proj2_sig i arg), f_ebody_match_spec; assumption.
  Qed.

  Lemma f_extract_oracle_free:
    forall x : f_arg_t sg, CP.oracle_free (proj1_sig i x).
  Proof.
    intro; apply (proj2_sig i x).
  Qed.
End FunImplBody.

(* Constructors *)

Section Ret.
  Section Impl.
    Context [A : Type] (x : A) (pt : A -> list Vprop.t).

    Inductive Ret_Spec (ctx : CTX.t) (F : i_spec_t A ctx) : Prop
      := Ret_SpecI
      (sels : Tuple.t (map Vprop.ty (pt x))):
      let pre := VpropList.inst (pt x) sels in forall
      (IJ : InjPre_Frame_Spec pre ctx {|
        sf_csm  := Sub.const pre true;
        sf_prd  := pt;
        sf_spec := FP.Ret (TF.mk (fun x => VpropList.sel (pt x)) x sels);
      |} F),
      Ret_Spec ctx F.

    Program Definition Ret0 : instr A := {|
      i_impl := CP.Ret x;
      i_spec := fun ctx => Ret_Spec ctx;
    |}.
    Next Obligation.
      destruct SP; apply (Tr_InjPre_Frame IJ).
      do 2 intro; cbn.
      apply SP.CRet.
      Apply sels.
      Apply. assumption.
      unfold Sub.neg, Sub.const;
      rewrite Vector.map_const, Sub.sub_const_false,
              CTX.sl_app, TF.to_of_tu.
      SL.normalize; reflexivity.
    Qed.
  End Impl.

  Definition Ret [A : Type] (x : A) {pt : opt_arg (A -> list Vprop.t) (fun _ => [])}
    : instr A
    := Ret0 x pt.

  Definition RetG [A : Type] [P : A -> Type] (x : A) (y : P x)
      {pt : opt_arg (forall x : A, P x -> list Vprop.t) (fun _ _ => [])}
    : instr (CP.sigG A P)
    := Ret0 (CP.existG P x y) (CP.split_sigG pt).
End Ret.
Section Bind.
  Context [A B : Type] (f : instr A) (g : A -> instr B).
  
  Inductive Bind_Spec (ctx : CTX.t) : i_spec_t B ctx -> Prop
    := Bind_SpecI : forall
    (s_fp : {s_f : i_spec_t A ctx | HasSpec f ctx s_f}),
    let s_f := proj1_sig s_fp in
    let f_prd (r : sf_rvar_t s_f) :=
      Sub.app (Sub.const (sf_prd_ctx s_f r) true)
              (Sub.const (CTX.sub ctx (Sub.neg (sf_csm s_f))) false)
    in forall
    (s_gp : forall r : sf_rvar_t s_f,
            let ctx1 := sf_post_ctx s_f r in
            {s_g : i_spec_t B ctx1 | HasSpec (g (TF.v_val r)) ctx1 s_g}),
    let s_g := fun (r : sf_rvar_t s_f) => add_csm (proj1_sig (s_gp r)) (f_prd r)
    in forall
    (csm : Sub.t ctx)
    (CSM : forall r : sf_rvar_t s_f,
      Sub.pull (sf_csm s_f) (Sub.const _ true) (snd (Sub.split _ _ (sf_csm (s_g r))))
      = csm)
    (prd : B -> VpropList.t)
    (PRD : forall r, sf_prd (s_g r) = prd)
    (spec : FP.instr (TF.mk_p B (fun y => VpropList.sel (prd y))))
    (SPEC : FP.eqv spec (
                let TF_A     := TF.mk_p A (sf_rsel s_f) in
                let TF_B prd := TF.mk_p B (fun y => VpropList.sel (prd y)) in
                @FP.Bind TF_A (TF_B prd)
                    (sf_spec s_f)
                    (TF.of_fun (T := TF_A) (fun r =>
                      eq_rect _ (fun prd => FP.instr (TF_B prd))
                        (sf_spec (s_g r)) _ (PRD r)))
            )),
    Bind_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := prd;
      sf_spec := spec
    |}.
  
  Program Definition Bind : instr B := {|
    i_impl := CP.Bind (i_impl f) (fun x => i_impl (g x));
    i_spec := fun ctx => Bind_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro.
    apply SPEC in PRE; clear SPEC.
    assert (s_g_sound : forall r : sf_rvar_t s_f, sound_spec (i_impl (g (TF.v_val r))) _ (s_g r)).
      { intros; apply Tr_add_csm, (proj2_sig (s_gp r)). }
    assert (s_g_csm : forall r, exists csm,
        sf_csm (s_g r) = Sub.app (Sub.const _ true) csm). {
      intro; exists (snd (Sub.split _ _ (sf_csm (proj1_sig (s_gp r))))).
      unfold s_g, f_prd; simpl; clear.
      rewrite (Sub.app_split _ _ (sf_csm (proj1_sig (s_gp r)))) at 1.
      unfold Sub.const, Sub.or.
      etransitivity. apply Sub.map2_app.
      f_equal; apply Vector.ext; intro k;
        erewrite Vector.nth_map2, !Vector.const_nth by reflexivity;
        destruct (Vector.nth _ k); reflexivity.
    }
    clearbody s_g; clear s_gp.
    eapply SP.Bind.
    - apply (proj2_sig s_fp).
      simpl in PRE; apply PRE.
    - clear PRE.
      intro x; unfold sf_post; simpl.
      apply SP.ExistsE; intro sels0.
      apply SP.PureE; simpl; rewrite TF.to_of_fun.
      set (r := existT _ x _).
      intro PRE.
      destruct (PRD r); simpl in PRE.
      eapply SP.Cons.
        { apply (s_g_sound r), PRE. }
      clear PRE.
      split. reflexivity.
      intro y; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      Intro sels1.
      Intro POST.
      Apply sels1.
      Apply POST.
      rewrite <- (CSM r).
      ecase s_g_csm as [g_csm E]. unfold sf_post_ctx in *; erewrite E.
      clear.
      rewrite !CTX.sl_app. apply SLprop.star_morph_imp. reflexivity.
      rewrite Sub.split_app; simpl.
      unfold Sub.neg, Sub.const.
      rewrite Sub.map_app, Sub.sub_app, Sub.map_pull, !Vector.map_const; simpl.
      rewrite Sub.sl_pull.
      rewrite !Sub.sub_const_false; simpl; SL.normalize; reflexivity.
  Qed.

  Local Opaque TF.of_fun TF.to_fun.

  Lemma Bind_SpecI1
    [ctx : CTX.t]
    [s_f : i_spec_t A ctx]
    (S_F : HasSpec f ctx s_f)
    [f_prd : TF.arrow (sf_rvar s_f) (fun r => Sub.t (sf_post_ctx s_f r))]
    (F_PRD : TF.arrow (sf_rvar s_f) (fun r =>
              Sub.app (Sub.const (sf_prd_ctx s_f r) true)
                      (Sub.const (CTX.sub ctx (Sub.neg (sf_csm s_f))) false) =
              TF.to_fun f_prd r))
    [s_g0 : TF.arrow (sf_rvar s_f) (fun r => i_spec_t B (sf_post_ctx s_f r))]
    (S_G0 : TF.arrow (sf_rvar s_f) (fun r =>
              HasSpec (g (TF.v_val r)) _ (TF.to_fun s_g0 r)))
    [s_g  : TF.arrow (sf_rvar s_f) (fun r => i_spec_t B (sf_post_ctx s_f r))]
    (S_G  : TF.arrow (sf_rvar s_f) (fun r =>
              add_csm (TF.to_fun s_g0 r) (TF.to_fun f_prd r) = TF.to_fun s_g r))
    [csm  : Sub.t ctx]
    (CSM  : TF.arrow (sf_rvar s_f) (fun x =>
              Sub.pull (sf_csm s_f)
                (Sub.const (Sub.sub ctx (sf_csm s_f)) true)
                (snd (Sub.split (VpropList.inst (sf_prd s_f (TF.v_val x)) (TF.v_sel x))
                                (CTX.sub ctx (Sub.neg (sf_csm s_f))) 
                                (sf_csm (TF.to_fun s_g x)))) = csm))
    [prd : B -> VpropList.t]
    (PRD : TF.arrow (sf_rvar s_f) (fun x => sf_prd (TF.to_fun s_g x) = prd))
    [spec : FP.instr (TF.mk_p B (fun y => VpropList.sel (prd y)))]
    (SPEC : spec = 
        let TF_A := sf_rvar s_f in
        let TF_B (prd : B -> VpropList.t) :=
          TF.mk_p B (fun y : B => VpropList.sel (prd y)) in
        FP.Bind (sf_spec s_f)
           (TF.of_fun (fun x =>
              eq_rect (sf_prd (TF.to_fun s_g x))
                (fun prd0 : B -> VpropList.t => FP.instr (TF_B prd0))
                (sf_spec (TF.to_fun s_g x)) prd
                (TF.to_fun PRD x)))):
    Bind_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := prd;
      sf_spec := spec;
    |}.
  Proof.
    unshelve refine (Bind_SpecI ctx (exist _ s_f S_F) _ csm _ prd _ spec _).
    - intro r.
      exists (TF.to_fun s_g0 r).
      exact  (TF.to_fun S_G0 r).
    - intro r; simpl.
      apply TF.to_fun with (x := r) in CSM as <-.
      rewrite <- (TF.to_fun PRD   r),
              <- (TF.to_fun S_G   r),
              <- (TF.to_fun F_PRD r).
      reflexivity.
    - intro r; simpl.
      apply TF.to_fun with (x := r) in CSM as <-.
      rewrite <- (TF.to_fun S_G   r),
              <- (TF.to_fun F_PRD r).
      reflexivity.
    - unfold FP.eqv; subst spec; simpl; intro.
      clear CSM S_F S_G0.
      apply FP.Spec.wp_morph. apply FP.wlp_monotone.
      intro r; rewrite !TF.to_of_fun; simpl in *.
      revert post.

      set (x_PRD := TF.to_fun (T := sf_rvar s_f) PRD r).
      clearbody x_PRD; clear PRD.
      case x_PRD; simpl; clear x_PRD.

      set (x_S_G := TF.to_fun (T := sf_rvar s_f) S_G r).
      clearbody x_S_G; clear S_G.
      case x_S_G; clear x_S_G s_g.

      set (x_F_PRD := TF.to_fun (T := sf_rvar s_f) F_PRD r).
      clearbody x_F_PRD; clear F_PRD.
      case x_F_PRD; clear x_F_PRD f_prd; simpl.

      reflexivity.
  Qed.
End Bind.
Section Branch.
  Inductive branch_collect_csm [ctx] (csm : Sub.t ctx) (csms : list (Sub.t ctx)) : Prop :=
    branch_collect_csmI.

  Lemma intro_TrSpec_branch [A ctx csm0 csms1 csm1 prd0 prd1 f0] f1
    (C : branch_collect_csm csm0 csms1)
    (E : csm1 = List.fold_left (@Sub.or ctx) csms1 (Sub.const ctx false))
    (T : TrSpec (mk_i_spec csm0 prd0 f0) (mk_i_spec csm1 prd1 f1)):
    @TrSpec A ctx (mk_i_spec csm0 prd0 f0) (mk_i_spec csm1 prd1 f1).
  Proof. exact T. Qed.

  Lemma TrSpec_branch_0 [A ctx s0 s1]
    (E : s1 = add_csm s0 (sf_csm s1)):
    @TrSpec A ctx s0 s1.
  Proof.
    rewrite E; apply Tr_add_csm.
  Qed.
End Branch.
Section Call.
  Import Spec.
  Section Spec.
    Context [res_t : Type] [ghout_t : option (res_t -> Type)]
            (s : @Spec.t_r0 res_t ghout_t).

    Let AG := opt_sigG ghout_t.

    Local Lemma vpost_eq
      (sel0 : Spec.sel0_t s) (xG : AG)
      (sel1 : Tuple.t (Spec.sel1_t (s sel0 xG)))
      (REQ  : Spec.req (s sel0)):
      VpropList.of_ctx (post (s sel0 xG sel1 REQ)) = Spec.vpost (s sel0 xG).
    Proof.
      apply VpropList.of_inst.
    Defined.

    Inductive Call_Spec (ctx : CTX.t) (F : i_spec_t AG ctx) : Prop
      := Call_SpecI
      (sel0 : Spec.sel0_t s):
      let ppre := Spec.pre (s sel0) ++ Spec.prs (s sel0)                      in
      let TF_A := TF.mk_p AG (fun x => Spec.sel1_t (s sel0 x))                in
      let TF_B := TF.mk_p AG (fun x => VpropList.sel (Spec.vpost (s sel0 x))) in
      forall
      (IJ : InjPre_Frame_Spec ppre ctx {|
        sf_csm  := Sub.app (Sub.const (Spec.pre (s sel0)) true)
                           (Sub.const (Spec.prs (s sel0)) false);
        sf_prd  := fun xG => Spec.vpost (s sel0 xG);
        sf_spec :=
          FP.Bind
            (@FP.Call TF_A {|
                FP.Spec.pre  := Spec.req (s sel0);
                FP.Spec.post := TF.of_fun (fun (r : TF.t TF_A) (REQ : Spec.req (s sel0)) =>
                  Spec.ens (s sel0 (TF.v_val r) (TF.v_sel r) REQ));
             |})
            (fun REQ => TF.of_fun (T := TF_A) (fun r =>
             FP.Ret (TF.mk _ (TF.v_val r)
              (eq_rect _ VpropList.sel_t
                       (VpropList.sel_of_ctx (Spec.post (s sel0 (TF.v_val r) (TF.v_sel r) REQ)))
                       _ (vpost_eq sel0 (TF.v_val r) (TF.v_sel r) REQ)))))
      |} F),
      Call_Spec ctx F.
  End Spec.
  Section Impl.
    Context (f : fid) [sg : f_sig] (HSIG : SIG f = Some sg) (sgh : f_sigh sg)
            (x : f_arg_t sg).

    Let AG := opt_sigG (f_ghout_t sgh).

    Definition Call_impl : @CP.instr SIG AG.
    Proof.
      unfold AG, opt_sigG.
      case f_ghout_t as [GO|].
      - exact (CP.Bind (CP.Call f HSIG x) (fun r =>
               CP.Bind (CP.Oracle (GO r)) (fun go =>
               CP.Ret (CP.existG _ r go)))).
      - exact (CP.Call f HSIG x).
    Defined.

    Variables (gi : OptTy.t (f_ghin_t_x sgh x)) (s : sigh_spec_t sgh x).
    Hypothesis (HSPC : fun_has_spec CT f HSIG s).

    Lemma Call_impl_sls sel0 REQ:
      SP.sls SPC Call_impl
        (Expanded.tr_1 (fun pt xG => pt xG)
          (Expanded.f_r1 (Expanded.to_expanded s gi) sel0)
          REQ).
    Proof.
      ecase HSPC as (ss & LEss & Hss).
        { exists gi, sel0, REQ. reflexivity. }
      clear HSPC. unfold Call_impl, sigh_spec_t in *.
      destruct f_ghout_t.
      - eapply SP.Bind.
        { eapply SP.Cons, LEss. apply SP.Call, Hss. }
        intro r; cbn.
        apply SP.ExistsE; intro go.
        eapply SP.Bind.
        { apply SP.Oracle with (x := go). }
        intro; apply SP.PureE; intros ->.
        apply SP.CRet; reflexivity.
      - eapply SP.Cons. { apply SP.Call, Hss. }
        rewrite LEss; unfold Expanded.tr_1; split; cbn. reflexivity.
        intro; Intro; reflexivity.
    Qed.

    Program Definition Call : instr AG := {|
      i_impl := Call_impl;
      i_spec := fun ctx => Call_Spec (s gi) ctx;
    |}.
    Next Obligation.
      destruct SP.
      apply (Tr_InjPre_Frame IJ); clear IJ.
      do 2 intro; cbn in *.
      case PRE as (REQ & POST).
      eapply SP.Cons.
        { apply Call_impl_sls. }
      split; cbn.
      - unfold ppre; rewrite CTX.sl_app.
        reflexivity.
      - intro rx; unfold Expanded.tr_post; cbn; SL.normalize.
        Intro sel1.
        Intro ENS.
        specialize (POST (TF.mk _ rx sel1));
          cbn in POST;
          rewrite !TF.to_of_fun, TF.to_of_tu in POST.
        EApply.
        Apply (POST ENS).
        clear post0 ENS POST; subst TF_A TF_B; cbn.
        case (vpost_eq (s gi) sel0 rx sel1 REQ); cbn.
        rewrite TF.to_of_tu, VpropList.inst_of_ctx, CTX.sl_app.
        unfold Sub.neg, Sub.const, ppre; cbn.
        rewrite Sub.map_app, !Vector.map_const, Sub.sub_app,
                Sub.sub_const_true, Sub.sub_const_false.
        reflexivity.
    Qed.
  End Impl.

  Definition Call_f_decl [sg sgh s] (fd : @f_decl sg sgh CT s)
    (x : f_arg_t sg)
    : OptTy.arrow (f_ghin_t_x sgh x)
                  (fun _ => instr (Spec.opt_sigG (f_ghout_t sgh)))
    :=
    OptTy.of_fun (fun gi =>
      Call (fd_id fd) (fd_Hsig (fd_H fd)) sgh x gi (s x) (fd_Hspec (fd_H fd) x)).
 
  Section Ghost.
    Context [sg : f_sig] [s : ghost_spec sg] (L : ghost_lem s) (x : f_arg_t sg).
    Program Definition gLem : instr (f_ret_t sg) := {|
      i_impl := CP.Oracle (f_ret_t sg);
      i_spec := fun ctx => Call_Spec (s x tt) ctx;
    |}.
    Next Obligation.
      destruct SP.
      apply (Tr_InjPre_Frame IJ); clear IJ.
      do 2 intro; cbn in *.
      case PRE as (REQ & WLP).
      specialize (L _ _ REQ).
      eapply SP.Cons with (s0 := SP.Spec.mk _ _); cycle 1.
      - split; [cbn; exact L | intro;reflexivityR].
      - clear L.
        apply SP.ExistsE; intro res.
        apply SP.ExistsE; intro sel1.
        specialize (WLP (TF.mk _ res sel1)).
        apply SP.COracle with (x := res); cbn in *.
        rewrite !TF.to_of_fun, TF.to_of_tu in WLP.
        Intro ENS%WLP; clear WLP.
        cbn in ENS.
        EApply; Apply ENS.
        clear.
        rewrite TF.to_of_tu.
        destruct vpost_eq; cbn.
        unfold Sub.neg, Sub.const, ppre.
        rewrite VpropList.inst_of_ctx, Sub.map_app, !Vector.map_const, Sub.sub_app,
                Sub.sub_const_true, Sub.sub_const_false.
        reflexivity.
    Qed.
  End Ghost.
End Call.
End VProg.

Global Arguments Ret [_ _] _ {pt}.
Global Arguments RetG [_ _ _] _ _ {pt}.
Global Arguments Bind [_ _ _] _ _.
Global Arguments Call [_ _ _ _] _ _ _ [_] _.
Global Arguments Call_f_decl [_ _ _ _] _ _.
Global Arguments gLem [_ _ _] _ _.


Module NotationsDef.
  (* types notation *)

  Record FDecl (arg_t : Type) (ghin_t  : option (arg_t -> Type))
               (ret_t : Type) (ghout_t : option (ret_t -> Type))
               (e : f_spec_exp (mk_f_sigh (mk_f_sig arg_t ret_t) ghin_t ghout_t))
    : Type := mk_FDecl {
    fd_FSpec : FSpec _ e
  }.
  Global Arguments fd_FSpec [_ _ _ _ _].

  Definition fd_sig
    [arg_t ghin_t ret_t ghout_t e] (F : @FDecl arg_t ghin_t ret_t ghout_t e)
    : f_sig := mk_f_sig arg_t ret_t.

  Definition fd_cp
    [arg_t ghin_t ret_t ghout_t e] (F : @FDecl arg_t ghin_t ret_t ghout_t e)
    : CP.f_spec (fd_sig F) := cp_f_spec (m_spec (fd_FSpec F)).

  Definition to_f_decl
    [arg_t ghin_t ret_t ghout_t e] (F : @FDecl arg_t ghin_t ret_t ghout_t e)
    (CT : CP.context)
    : Type := f_decl CT (m_spec (fd_FSpec F)).

  Definition fd_mk (f : fid)
    [arg_t ghin_t ret_t ghout_t e] (F : @FDecl arg_t ghin_t ret_t ghout_t e)
    (CT : CP.context)
    (HSIG : projT1 CT f = Some (fd_sig F))
    (HSPS : CP.fun_has_spec (projT2 CT) f HSIG = fd_cp F):
    to_f_decl F CT.
  Proof.
    exists f. unshelve eapply cp_is_declared; assumption.
  Defined.

  Definition Call_to_f_decl
    [arg_t ghin_t ret_t ghout_t e F CT] (fd : @to_f_decl arg_t ghin_t ret_t ghout_t e F CT)
    (x : arg_t) : OptTy.arrow (option_map (fun gi => gi x) ghin_t) (fun _ => instr CT (Spec.opt_sigG ghout_t))
    := Call_f_decl fd x.

  Coercion to_f_decl      : FDecl     >-> Funclass.
  Coercion Call_to_f_decl : to_f_decl >-> Funclass.


  Record LDecl (arg_t : Type) (ret_t : Type) (e : f_spec_exp (lem_sigh (mk_f_sig arg_t ret_t)))
    : Type := mk_LDecl {
    ld_FSpec : FSpec _ e
  }.
  Global Arguments ld_FSpec [_ _ _].

  Definition to_ghost_lem [arg_t ret_t e] (L : @LDecl arg_t ret_t e)
    : Type := ghost_lem (m_spec (ld_FSpec L)).

  (* NOTE it does not seem possible to declare a coercion from [to_ghost_lem] to Funclass
     with implicit [CT] (see https://github.com/coq/coq/issues/5527).
     One has to use an explicit conversion [gLem]. *)
  Coercion to_ghost_lem : LDecl >-> Sortclass.


  Definition FImpl [CT sg sgh s] (fd : @f_decl sg sgh CT s) : Type
    := f_body CT sgh.

  Definition FCorrect [CT sg sgh s fd] (fi : @FImpl CT sg sgh s fd) : Prop
    := f_body_match fi s.
End NotationsDef.

Section F_ENTRY.
  Import NotationsDef.

  Context [arg_t ghin_t ret_t ghout_t e] (F : FDecl arg_t ghin_t ret_t ghout_t e).

  Definition f_entry [A : CP.context -> Prop] (C : forall CT, A CT): CP.context_entry
    := {| CP.ce_sig := fd_sig F; CP.ce_spec := fd_cp F |}.

  Lemma has_f_entry [CT f A] C (H : CP.context_has_entry CT f (@f_entry A C)):
    to_f_decl F CT.
  Proof.
    exact (fd_mk f F CT (proj1_sig H) (proj2_sig H)).
  Defined.

  Definition f_entry_extract [CT A C] [impl : f_body CT _] [r]
    (CR : f_body_match impl (m_spec (fd_FSpec F)))
    (EX : f_extract impl)
    (E  : r = proj1_sig EX):
    CP.entry_impl_correct CT (@f_entry A C) r.
  Proof.
    rewrite E; split.
    - apply f_extract_match_spec, CR.
    - apply f_extract_oracle_free.
  Defined.
End F_ENTRY.

Module Tac.
  Export Util.Tac.

  (* If [t] is a term with a destructive let [let (...) := ?u in _] as head,
     partially instantiate [?u] by applying the constructor, allowing the let to be reduced. *)
  Ltac build_matched_shape t :=
    lazymatch t with (match ?p with _ => _ end) =>
      build_term p ltac:(fun _ => econstructor; shelve)
    end.
  
  Ltac case_until_triv :=
    try solve [split];
    let i := fresh "i" in
    intros [|i]; [|revert i; case_until_triv].


  Ltac of_expanded_arg :=
    lazymatch goal with |- _ (match ?x with _ => _ end) ?s =>
      Tac.build_term s ltac:(fun _ => destruct x; shelve);
      destruct x;
      cbn;
      of_expanded_arg
    | _ => idtac
    end.

  Local Lemma mk_red_FSpec [sg : f_sig] [sgh : f_sigh sg] [e : f_spec_exp sgh]
    [s0 s1 : f_spec sgh]
    (E : forall x : f_arg_t sg, Spec.Expanded.of_expanded (e x) (s0 x))
    (R : s1 = s0):
    FSpec sgh e.
  Proof.
    exists s1.
    rewrite R; exact E.
  Defined.

  (* solves a goal [FSpec sig espec] *)
  Ltac build_FSpec :=
    refine (mk_red_FSpec _ _);
    [ cbn;
      intro (* arg  *); of_expanded_arg;
      intro (* gi   *); of_expanded_arg;
      refine (Spec.Expanded.of_expanded0I _ _ _); cbn;
      intro (* sel0 *); of_expanded_arg;
      refine (Spec.Expanded.of_expanded1I _ _ _); cbn;
      (* ret, TODO? allow matching *)
      try lazymatch goal with |- forall x, _ (match x with _ => _ end) _ =>
        idtac "WARNING: matching on the returned value is not supported, use projections instead"
      end;
      intro (* ret *);
      simple refine (Spec.Expanded.of_expanded2I _ _ _ _ _ _);
      [ shelve | shelve | shelve | shelve
      | (* sel1_TU_GOAL *) cbn; intro (* sel1 *); Tuple.build_type_iso_tu
      | shelve | (* S_VPOST *) Tac.cbn_refl
      | shelve | (* S3      *) cbn; repeat intro; refine (Spec.Expanded.of_expanded3I _) ]
    | cbn; reflexivity ].

  (* solves a goal [FDecl arg_t ghin_t ret_t ghout_t espec] *)
  Ltac build_FDecl :=
    constructor; Tac.build_FSpec.

  (* solves a goal [LDecl arg_t ret_t espec] *)
  Ltac build_LDecl :=
    constructor; Tac.build_FSpec.


  (* build_HasSpec *)

  Local Lemma change_arg [A : Type] [f : A -> Type] (x0 x1 : A)
    (F : f x0)
    (E : x0 = x1):
    f x1.
  Proof.
    rewrite <- E; exact F.
  Qed.

  Local Lemma intro_i_spec_t_eq [A : Type] [ctx : CTX.t] [s0 : i_spec_t A ctx] [csm1 prd1] f1
    (E : csm1 = sf_csm s0 /\
         { E : prd1 = sf_prd s0
             | f1 = eq_rect_r (fun prd => FP.instr (TF.mk_p A (fun x => VpropList.sel (prd x))))
                              (sf_spec s0) E}):
    s0 = mk_i_spec csm1 prd1 f1.
  Proof.
    destruct s0; cbn in *.
    case E as [-> [E ->]].
    destruct E.
    reflexivity.
  Qed.

  Ltac build_i_spec_t_eq :=
    simple refine (intro_i_spec_t_eq _ _); cbn;
    refine (conj eq_refl (exist _ eq_refl _));
    cbn; reflexivity.

  (* solves a goal [TrSpec SPEC s (mk_i_spec csm prd ?f)] *)
  Ltac build_Tr_change_exact :=
    simple refine (Tr_change_exact _ _ _ _ _ _);
    [ shelve
    | (* CSM  *) Tac.cbn_refl
    | (* S1   *) Tac.cbn_refl
    | (* rsel *) cbn; repeat intro; Tuple.build_shape
    | (* RSEL *) cbn; repeat intro; CTX.Inj.build_beq
    | (* F1   *) Tac.cbn_refl ].

  (* solves a goal [InjPre_Spec m ctx ?add F ?F']
     Leaves a goal [?F' = _]. *)
  Ltac build_InjPre :=
    refine (InjPre_SpecI _ _ _ _ _ _ _ _);
    [ (* ij *) CTX.Inj.build_itrf |].

  (* solves a goal [InjPre_Frame_Spec m ctx F ?F']
     Leaves a goal [?F' = _] *)
  Ltac build_InjPre_Frame :=
    refine (InjPre_Frame_SpecI _ _ _ _ _ _);
    build_InjPre.


  (* Tactics to build the instruction specifications. *)
  Global Create HintDb HasSpecDB discriminated.
  Global Hint Constants Opaque : HasSpecDB.
  Global Hint Variables Opaque : HasSpecDB.

  Ltac build_Ret :=
    simple refine (Ret_SpecI _ _ _ _ _ _);
    [ (* sels *) Tuple.build_shape
    | (* IJ   *) build_InjPre_Frame; cbn_refl ].

  Ltac build_Bind_init :=
    simple refine (Bind_SpecI1 _ _ _ _ _ _ _ _ _ _);
    [ shelve | | shelve | | shelve | | shelve |
    | shelve | | shelve | | shelve | ].

  Ltac build_Bind build_f :=
    build_Bind_init;
    [ (* S_F   *) build_f tt
    | (* F_PRD *) cbn_refl
    | (* S_G0  *) cbn; repeat intro; build_f tt
    | (* S_G   *) cbn_refl
    | (* CSM   *) cbn_refl
    | (* PRD   *) cbn_refl
    | (* SPEC  *) cbn_refl ].

  Ltac build_Call :=
    simple refine (Call_SpecI _ _ _ _ _);
    [ shelve
    | (* IJ *)
      cbn;
      repeat lazymatch goal with |- InjPre_Frame_Spec (Spec.pre ?x ++ _) _ _ _ =>
        build_matched_shape x; cbn
      end;
      build_InjPre_Frame; cbn_refl ].

  (* TODO: be more careful about the dependencies on the matched term in the vprog and in the context *)

  (* destructive let *)
  Ltac build_HasSpec_dlet build_f x s :=
    simple refine (change_arg _ s _ _);
    [ destruct x; shelve
    | destruct x; cbn; build_f tt
    | simple refine (intro_i_spec_t_eq _ _);
    [ (* sf_csm *) clear; shelve | shelve | (* sf_spec *) destruct x; shelve
      | destruct x; cbn;
        refine (conj eq_refl (exist _ eq_refl _));
        cbn; reflexivity ] ].

  Ltac build_HasSpec_branch build_f x :=
    refine (transform_spec _ _ _);
    [ (* For each branch a specification where [sf_csm] and [sf_prd] do not depend on the
         arguments of the matched value. *)
      lazymatch goal with |- HasSpec _ _ _ ?s =>
        Tac.build_term s ltac:(fun _ =>
          simple refine (mk_i_spec _ _ _);
          [ (* sf_csm  *) cbn; Tac.const_case x; clear
          | (* sf_prd  *) cbn; Tac.const_case x; try clear x
          | (* sf_spec *) case x; try clear x ];
        shelve)
      end;
      cbn;
      destruct x;
      (simple refine (change_arg _ _ _ _);
       [ shelve | build_f tt | Tac.build_i_spec_t_eq ])
    | (* transforms the several specifications into a common one *)
      cbn;
      simple refine (intro_TrSpec_branch _ _ _ _ _);
      [ (* csms1 *) clear; shelve | (* csm1 *) clear; shelve | shelve
      | (* f1 *) Tac.nondep_case x; try clear x; shelve
      | (* C  *)
        case x; repeat intros _;
        lazymatch goal with |- branch_collect_csm ?c ?cs =>
          Tac.elist_add cs c; constructor
        | |- ?g => idtac "build_HasSpec_branch::branch_collect_csm" g
        end
      | (* E  *)
        match goal with |- _ = List.fold_left _ ?cs _ =>
          Tac.elist_end cs
        end;
        Tac.cbn_refl
      | (* T  *)
        cbn;
        case x; repeat intro;
        (* first branch *)
        [ refine (TrSpec_branch_0 _ _); Tac.build_i_spec_t_eq | ..];
        (* other branches *)
        build_Tr_change_exact
      ]
    ].

  (* solves a goal [HasSpec i ctx ?s] *)
  Ltac build_HasSpec :=
    let rec build _ :=
    lazymatch goal with |- @HasSpec ?C ?A ?i ?ctx ?s =>
    let i' := eval hnf in i in
    change (@HasSpec C A i' ctx s);
    lazymatch i' with
    | mk_instr _ =>
        refine (HasSpec_ct _ _);
        hnf;
        lazymatch goal with
        | |- Ret_Spec    _ _ _ _ => build_Ret
        | |- Bind_Spec _ _ _ _ _ => build_Bind build
        | |- Call_Spec     _ _ _ => build_Call
        | |- ?g => try solve [eauto 1 with HasSpecDB nocore];
                   fail "HasSpec::ct" g
        end
    | (match ?x with _ => _ end) =>
        tryif is_single_case x
        then build_HasSpec_dlet   build x s (* destructive let *)
        else build_HasSpec_branch build x   (* multiple branches *)
    | ?g => fail "HasSpec" g
    end end
    in build tt.
  
  (* solves a goal [HasSpec i ctx (mk_i_spec csm prd ?f)] *)
  Ltac build_HasSpec_exact :=
    refine (transform_spec _ _ _);
    [ build_HasSpec
    | build_Tr_change_exact ].


  Local Lemma elim_tuple_eq_conj [TS] [u v : Tuple.t TS] [P Q : Prop]
    (C : elim_and_list_f (List.rev_append (Tuple.eq_list u v) nil) Q):
    (Tuple.typed_eq u v /\ P) -> Q.
  Proof.
    rewrite <- List.rev_alt, elim_and_list, and_list_rev, <- Tuple.eq_iff_list in C.
    intros [[] _]; auto.
  Qed.

  Local Lemma simpl_tuple_eq_conj [TS] [u v : Tuple.t TS] [P Q : Prop] [xs : list Prop]
    (E0 : and_list_eq (Tuple.eq_list u v) xs)
    (E1 : and_list xs = Q):
    (Tuple.typed_eq u v /\ P) <-> (Q /\ P).
  Proof.
    case E1, E0 as [<-].
    rewrite <- Tuple.eq_iff_list.
    split.
    - intros ([] & ?); tauto.
    - repeat split; tauto.
  Qed.

  (* solves a goal [(exists x0...x9, Tuple.typed_eq (x0...x9) u /\ P) <-> ?Q]
     by simplifying the lhs. *)
  Ltac simplify_ex_eq_tuple :=
    etransitivity;
    [ repeat first [
        (* remove an [exists x] if we have an equality [x = _] *)
        etransitivity; [
        refine (exists_eq_const _ _ (fun x => _));
        repeat refine (ex_ind (fun x => _));
        refine (elim_tuple_eq_conj _);
        cbn; repeat intro; eassumption
        |]
      | (* otherwise, conitinue with the next [exists] *)
        refine (Morphisms_Prop.ex_iff_morphism _ _ (fun x => _))
      | (* if no more [exists] remains *)
        reflexivity
      ]
    | cbn;
      repeat refine (Morphisms_Prop.ex_iff_morphism _ _ (fun x => _));
      refine (simpl_tuple_eq_conj _ _);
      (* remove trivial equalities [x = x] *)
      [ cbn;
        repeat first [ refine (simpl_and_list_r1 eq_refl _)
                     | refine (simpl_and_list_e1 _) ];
        exact simpl_and_list_0
      | cbn; reflexivity ]
    ].

  Ltac build_impl_match_init :=
    (* destruct arg *)
    cbn;
    repeat lazymatch goal with
    |- impl_match _ _ (match ?x with _ => _ end) => destruct x; cbn
    end;
    refine (intro_impl_match1 _ _ _ _); cbn;
    (* intro and destruct gi *)
    intro;
    repeat lazymatch goal with
    |- forall _ : Spec.sel0_t (match ?x with _ => _ end), _ => destruct x; cbn
    end;
    (* intro and destruct sel0 *)
    intro;
    repeat lazymatch goal with
    |- Impl_Match _ _ (match ?x with _ => _ end) => destruct x; cbn
    end;

    simple refine (@Impl_MatchI _ _ _ _ _ _ _ _ _ _);
    [ (* f *) shelve | (* F *) cbn | (* ex_sel1 *) shelve
    | (* EX_SEL1 *) cbn; repeat intro; simplify_ex_eq_tuple
    | (* WLP *) ].

  (* change a goal [impl_match CT vprog spec] into a condition [forall (REQ : req), wlp f post] *)
  Ltac build_impl_match :=
    build_impl_match_init;
    [ (* F   *) build_HasSpec_exact
    | (* WLP *) cbn ].

  Lemma extract_cont_change [SG A B i k] r0 [r1]
    (C : CP.extract_cont i k r0)
    (E : r0 = r1):
    @CP.extract_cont SG A B i k r1.
  Proof.
    subst; exact C.
  Qed.

  Ltac build_extract_cont :=
    cbn;
    lazymatch goal with
    | |- @CP.extract_cont ?SG ?A ?B (i_impl ?v) ?k ?i =>
        lazymatch v with
        | context[match ?x with _ => _ end] =>
            simple refine (extract_cont_change _ _ _);
            [ (* r0 *)
              destruct x; shelve
            | (* C *)
              destruct x;
              build_extract_cont
            | (* E *)
              (* tries to remove the match *)
              first [ destruct x; [reflexivity] | reflexivity ] ]
        | _ =>
            let v' := eval hnf in v in
            progress change (@CP.extract_cont SG A B (i_impl v') k i);
            build_extract_cont
        end
    | _ => CP.build_extract_cont_k build_extract_cont
    end.

  (* solves a goal [f_extract bd] *)
  Ltac extract_impl :=
    eexists; intro;
    refine (CP.extract_by_cont _ _ _);
    [ build_extract_cont
    | Tac.cbn_refl
    | try solve [ CP.build_oracle_free ] ].

  (* solves a goal [CP.entry_impl_correct CT (f_entry F PF) ?impl] *)
  Ltac build_f_entry_impl_correct :=
    match goal with |- CP.entry_impl_correct _ (f_entry _ ?C) _ =>
    simple refine (f_entry_extract _ _ _ _);
    [ shelve
    | unshelve eapply C; assumption
    | Tac.extract_impl
    | cbn; reflexivity ]
    end.

End Tac.

(* Exported tactics *)

Module ExtractTactics.
  #[export] Hint Extern 1 (Arrow (CP.context_has_entry _ _ (f_entry _ _)) _) =>
     exact (mk_Arrow (has_f_entry _ _)) : extractDB.
  
  #[export] Hint Extern 1 (CP.entry_impl_correct _ (f_entry _ _) _) =>
     Tac.build_f_entry_impl_correct : extractDB.
End ExtractTactics.
Export ExtractTactics.

Module Tactics.
  #[export] Hint Extern 1 (NotationsDef.FDecl _ _ _ _ _) => Tac.build_FDecl : DeriveDB.
  #[export] Hint Extern 1 (NotationsDef.LDecl     _ _ _) => Tac.build_LDecl : DeriveDB.

  #[export] Hint Extern 1 (f_extract _) => Tac.extract_impl : DeriveDB.

  (* Changes a goal [f_body_match impl spec] into a goal [pre -> FP.wlpa f post]
     where [f : FP.instr _] is a functionnal program. *)
  Ltac build_fun_spec :=
    intro (* arg *);
    Tac.build_impl_match;
    FP.simpl_prog.

  (* Changes a goal [f_body_match impl spec] into a WLP *)
  Ltac by_wlp :=
    build_fun_spec;
    FP.by_wlp_ false.

  Ltac solve_by_wlp :=
    build_fun_spec;
    FP.by_wlp_ false;
    FP.solve_wlp;
    eauto.

  (* start the proof of a ghost lemma *)
  Ltac init_lemma0 :=
    unfold NotationsDef.to_ghost_lem, ghost_lem; cbn.

  Tactic Notation "init_lemma" simple_intropattern_list(xs) :=
    init_lemma0;
    intros xs;
    cbn in *;
    try SL.normalize.
End Tactics.

Declare Custom Entry vprog_spec_0.
Declare Custom Entry vprog_spec_1.
Declare Custom Entry vprog_spec_2.

Module Notations.
  Export NotationsDef.

  (* vprop notation *)

  Notation "x ~> v" := (CTX.mka (x, v)) (at level 100).
  Notation "x ~>"   := (Vprop.mk x) (at level 100).
  Definition vptr := SLprop.cell.
  Global Arguments vptr/.

  (* instruction notation *)

  Notation "' x <- f ; g" := (Bind f (fun x => g))
    (at level 200, x pattern at level 0, only parsing).
  Notation "' x y <- f ; g" := (Bind f (fun '(CP.existG _ x y) => g))
    (at level 200, x pattern at level 0, y pattern at level 0, only parsing).
  Notation "f ;; g" := (Bind f (fun _ => g))
    (at level 199, right associativity, only parsing).

  (* specification notation *)

  Declare Scope vprog_spec_scope.
  Delimit Scope vprog_spec_scope with vprog_spec.
  Global Arguments FSpec [sg] sgh e%vprog_spec.
  Global Arguments FDecl (_ _ _ _)%type e%vprog_spec.
  Global Arguments LDecl (_ _)%type e%vprog_spec.


  Definition mk_f_r0_None [arg_t res_t ghout_t]
    (f : arg_t -> @Spec.Expanded.t_r0 res_t ghout_t):
    f_spec_exp (mk_f_sigh (mk_f_sig arg_t res_t) None ghout_t)
    := fun arg _ => f arg.
  Definition mk_f_r0_Some [arg_t ghin_t res_t ghout_t]
    (f : forall (x : arg_t) (y : ghin_t x), @Spec.Expanded.t_r0 res_t ghout_t):
    f_spec_exp (mk_f_sigh (mk_f_sig arg_t res_t) (Some ghin_t) ghout_t)
    := fun arg => f arg.

  Definition mk_f_r2_None [A : Type] [req : Prop] (f : A -> Spec.Expanded.t_r2 req)
    (x : @Spec.opt_sigG A None) : Spec.Expanded.t_r2 req :=
    f x.
  Definition mk_f_r2_Some [A : Type] [req : Prop] [GO : A -> Type]
    (f : forall (x : A) (y : GO x), Spec.Expanded.t_r2 req)
    (x : @Spec.opt_sigG A (Some GO)) : Spec.Expanded.t_r2 req :=
    CP.split_sigG f x.

  Global Arguments mk_f_r0_None/.
  Global Arguments mk_f_r0_Some/.
  Global Arguments mk_f_r2_None/.
  Global Arguments mk_f_r2_Some/.

  Notation "'SPEC' arg s" := (mk_f_r0_None (fun arg => s))
    (at level 0,
     arg pattern at level 0,
     s custom vprog_spec_0 at level 0) : vprog_spec_scope.
  Notation "'SPEC' arg & gi s" := (mk_f_r0_Some (fun arg gi => s))
    (at level 0,
     arg pattern at level 0, gi pattern at level 0,
     s custom vprog_spec_0 at level 0) : vprog_spec_scope.

  Notation "' sel0 prs pre req s" :=
    (Spec.Expanded.mk_r0 (fun sel0 =>
     Spec.Expanded.mk_r1 prs pre req s))
    (in custom vprog_spec_0 at level 0,
     sel0 pattern at level 0, prs constr at level 0, pre constr at level 0, req constr at level 0,
     s custom vprog_spec_1 at level 0).

  Notation "& REQ ' res & go sel1 s" :=
    (mk_f_r2_Some (fun res go =>
     Spec.Expanded.mk_r2 (fun sel1 REQ => s)))
    (in custom vprog_spec_1 at level 0,
     REQ name, res name, go name, sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).
  Notation "& REQ ' res sel1 s" :=
    (mk_f_r2_None (fun res =>
     Spec.Expanded.mk_r2 (fun sel1 REQ => s)))
    (in custom vprog_spec_1 at level 0,
     REQ name, res name, sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).
  Notation "' res & go sel1 s" :=
    (mk_f_r2_Some (fun res go =>
     Spec.Expanded.mk_r2 (fun sel1 _ => s)))
    (in custom vprog_spec_1 at level 0,
     res name, go name, sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).
  Notation "' res sel1 s" :=
    (mk_f_r2_None (fun res =>
     Spec.Expanded.mk_r2 (fun sel1 _ => s)))
    (in custom vprog_spec_1 at level 0,
     res name, sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).

  Notation "post ens" := (Spec.Expanded.mk_r3 post ens)
    (in custom vprog_spec_2 at level 0,
     post constr at level 0, ens constr at level 0).
End Notations.
