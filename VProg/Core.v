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

Local Transparent FP.Ret FP.Bind FP.Call FP.Assert.

(* Type family *)
Module TF.
  Include DTuple.

  (* The functional representation of a vprog instruction returns
     the value returned by the instruction |val] and the selectors
     of the produced vprops [sel], which can depend on [val].
     We represent this composite return value using a dependent tuple.
   *)

  Definition mk_p0 (p_val : Type) (p_sel : p_val -> list Type) : p :=
    Pcons p_val (fun x => p_tu (p_sel x)).

  Definition mk_p (p_val : Type) (p_sel : p_val -> VpropList.t) : p :=
    mk_p0 p_val (fun x => VpropList.sel (p_sel x)).
  Global Arguments mk_p/.

  Definition mk_t0 (p_val : Type) (p_sel : p_val -> list Type) : Type :=
    DTuple.t (mk_p0 p_val p_sel).
  
  Definition mk_t (p_val : Type) (p_sel : p_val -> VpropList.t) : Type :=
    DTuple.t (mk_p p_val p_sel).

  Definition mk0 [p_val : Type] (p_sel : p_val -> list Type)
    (v_val : p_val) (v_sel : Tuple.t (p_sel v_val)) : DTuple.t (mk_p0 p_val p_sel)
    := pair v_val (of_tu v_sel).
  Global Arguments mk0 _ _ _ _/.

  Definition mk [p_val : Type] (p_sel : p_val -> VpropList.t)
    (v_val : p_val) (v_sel : VpropList.sel_t (p_sel v_val)) : mk_t p_val p_sel
    := pair v_val (of_tu v_sel).
  Global Arguments mk/.

  Definition v_val [p_val p_sel] (v : t (mk_p0 p_val p_sel)) : p_val :=
    let '(existT _ x _) := v in x.

  Definition v_sel [p_val p_sel] (v : t (mk_p0 p_val p_sel)) : Tuple.t (p_sel (v_val v)) :=
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


  (* Value specification *)

  Section Value.
    Definition vpost_t := forall res : opt_sigG, VpropList.t.

    Definition val_pt (vpost : vpost_t) : Type :=
      forall (res : opt_sigG) (spost : VpropList.sel_t (vpost res)), Prop.

    Definition val_wp (vpost : vpost_t) : Type :=
      val_pt vpost -> Prop.

    Definition p_val_t : Type := vpost_t -> Type.

    Definition p_val_f (p_val : p_val_t) : Type :=
      forall vpost : vpost_t,
      p_val vpost -> val_wp vpost.
  End Value.

  (* Value specification using pre+post condition *)

  Section ValueSpec.
    Record t_vs1 (vp : VpropList.t) : Type := mk_vs1 {
      spost : VpropList.sel_t vp;      (* post condition selectors *)
      ens   : Prop;                    (* ensures *)
    }.
    Global Arguments mk_vs1 [vp] _ _.

    Definition post (vp : VpropList.t) (s : t_vs1 vp) : CTX.t :=
      VpropList.inst vp (spost s).

    Record t_vs0 (req : Prop) (vp : VpropList.t) : Type := mk_vs0 {
      sel1_t : list Type;              (* existentially quantified bound variables *)
      f_vs1  : Tuple.arrow sel1_t (fun _ => req -> t_vs1 vp);
    }.
    Global Arguments mk_vs0 [req vp] _ _.

    Definition f_vs1_f [req : Prop] [vp : VpropList.t] (s : t_vs0 req vp):
      forall (sel1 : Tuple.t (sel1_t s)) (REQ : req), t_vs1 vp :=
      Tuple.to_fun (f_vs1 s).

    Record t_vs (vpost : vpost_t) : Type := mk_vs {
      req   : Prop;  (* requires *)
      f_vs0 : forall res : opt_sigG, t_vs0 req (vpost res)
    }.
    Global Arguments mk_vs [vpost] _ _.

    Definition sem_vs : p_val_f t_vs :=
      fun (vpost : vpost_t) (vs : t_vs vpost) (pt : val_pt vpost) =>
      exists (REQ  : req vs),
      forall (res : opt_sigG),             let vs := f_vs0   vs res      in
      forall (sel1 : Tuple.t (sel1_t vs)), let vs := f_vs1_f vs sel1 REQ in
      ens vs -> pt res (spost vs).
  End ValueSpec.
  Coercion f_vs1_f : t_vs0 >-> Funclass.
  Coercion f_vs0   : t_vs  >-> Funclass.

  (* Value specification using a functional representation *)

  Section ValueFunc.
    Definition t_vf : p_val_t := fun vpost : vpost_t =>
      FunProg.instr (TF.mk_p opt_sigG vpost).

    Definition sem_vf : p_val_f t_vf :=
      fun (vpost : vpost_t) (vf : t_vf vpost) (pt : val_pt vpost) =>
      FunProg.wlp vf (fun x => pt (TF.v_val x) (TF.v_sel x)).
  End ValueFunc.

  (* Full specification *)

  Context (p_val : p_val_t).

  Record t_r1 : Type := mk_r1 {
    prs   : CTX.t;                     (* preserved *)
    pre   : CTX.t;                     (* pre condition *)
    vpost : opt_sigG -> VpropList.t;   (* post condition vprops *)
    val   : p_val vpost                (* value specification *)
  }.
  Global Arguments mk_r1 : clear implicits.

  Record t_r0 : Type := mk_r0 {
    sel0_t :  Type;                    (* universally quantified bound variables *)
    f_r1   :> sel0_t -> t_r1;
  }.
  Global Arguments mk_r0 : clear implicits.

  Definition t' : Type := ghin_t -> t_r0.
End Spec.
  Global Arguments t_vs   {A GO}.
  Global Arguments sem_vs {A GO}.
  Global Arguments t_vf   {A GO}.
  Global Arguments sem_vf {A GO}.

  Definition t (GI : option Type) (A : Type) (GO : option (A -> Type)): Type
    := @t' GI A GO t_vs.

  (* Semantics of a [Spec.t'], in separation logic *)

  Section Semantics.
    Context [GI : option Type] [A GO p_val] (p_sem : @p_val_f A GO p_val).

    (* Post-condition transformer *)
    Context [B] (PT : (opt_sigG GO -> SLprop.t) -> (B -> SLprop.t)).

    Definition tr_0 (vs : t_r0 p_val) (ss : SP.Spec.t B) : Prop :=
      exists (sel0 : sel0_t vs), let vs := vs sel0 in
      exists (pt : val_pt (vpost vs)),
      p_sem _ (val vs) pt /\
      SP.Spec.le {|
        SP.Spec.pre :=
          CTX.sl (pre vs) **
          CTX.sl (prs vs);
        SP.Spec.post := fun x => PT (fun xG : opt_sigG GO =>
          SLprop.ex (VpropList.sel_t (vpost vs xG)) (fun sel1 =>
          SLprop.pure (pt xG sel1) **
          CTX.sl (VpropList.inst (vpost vs xG) sel1)
          )) x **
          CTX.sl (prs vs)
      |}%slprop ss.

    Definition tr' (vs : @t' GI A GO p_val) (ss : SP.Spec.t B) : Prop :=
      exists (gi : ghin_t GI), tr_0 (vs gi) ss.
  End Semantics.

  Definition sem_pt_id {A GO} (pt : @opt_sigG A GO -> SLprop.t) : @opt_sigG A GO -> SLprop.t :=
    pt.

  Definition sem_pt_ex {A GO} (pt : @opt_sigG A GO -> SLprop.t) (x : A) : SLprop.t :=
    SLprop.ex (ghout_t GO x) (fun go => pt (to_opt_sigG (CP.existG _ x go))).

  Definition tr [GI A GO] : t GI A GO -> SP.Spec.t A -> Prop
    := @tr' GI A GO _ sem_vs _ sem_pt_ex.

Module Expanded. Section Expanded.
  (* The [Spec.t] type enforces syntactically some conditions:
     - The vprops of the postcondition do not depend on [sel1] (only their selectors can).
     - [sel1_t] is a tuple
     However, in order to provide a simpler interface for defining specifications,
     we also define a type [Spec.Expanded.t] that does not enforce those conditions.
     From a [Spec.Expanded.t] written by the user, we build a proved-equivalent [Spec.t] using tactics
     ([Tac.build_of_expanded]). The two conditions above are checked in the process.
   *)
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


  (* Semantics of a [Spec.Expanded.t], in separation logic *)
  Definition tr_post [req] (e : Expanded.t_r2 req) (REQ : req) : SLprop.t :=
    SLprop.ex (sel1_t e) (fun sel1 =>
      SLprop.pure (ens (e sel1 REQ)) **
      CTX.sl (post (e sel1 REQ)))%slprop.

  Definition tr_1
    (vs : Expanded.t_r1) (REQ : req vs) : SP.Spec.t A :=
    {|
      SP.Spec.pre  :=
        CTX.sl (pre vs) **
        CTX.sl (prs vs);
      SP.Spec.post := fun x =>
        SLprop.ex (ghout_t GO x) (fun go => let xG := to_opt_sigG (CP.existG _ x go) in
        tr_post (vs xG) REQ **
        CTX.sl (prs vs));
    |}%slprop.

  Definition tr (vs : t) (ss : SP.Spec.t A) : Prop :=
    exists (gi : ghin_t GI) (sel0 : sel0_t (vs gi)) (REQ : req (vs gi sel0)),
    SP.Spec.le (tr_1 (vs gi sel0) REQ) ss.


  (* We can always build a [Spec.Expanded.t] from a [Spec.t (p_val := t_vs)] *)
  Definition to_expanded2 [req vp] (s : Spec.t_vs0 req vp) : Expanded.t_r2 req :=
    @mk_r2 req (Tuple.t (Spec.sel1_t s)) (fun sel1 REQ =>
    mk_r3 (Spec.post (s sel1 REQ)) (Spec.ens (s sel1 REQ))).

  Definition to_expanded0 (s : Spec.t_r0 Spec.t_vs) : Expanded.t_r0 :=
    @mk_r0 (Spec.sel0_t s) (fun sel0 => let sv := Spec.val (s sel0) in
    mk_r1 (Spec.prs (s sel0)) (Spec.pre (s sel0)) (Spec.req sv) (fun xG =>
    to_expanded2 (sv xG))).

  Definition to_expanded (s : Spec.t GI A GO) : Expanded.t :=
    fun gi => to_expanded0 (s gi).

  (* For the reverse direction, we need to check some conditions *)
  Inductive of_expanded3 (e : Expanded.t_r3) : Spec.t_vs1 (VpropList.of_ctx (post e)) -> Prop
    := of_expanded3I:
    of_expanded3 e (Spec.mk_vs1 (VpropList.sel_of_ctx (post e)) (ens e)).

  Inductive of_expanded2 [req] (e : Expanded.t_r2 req) (vpost : VpropList.t): Spec.t_vs0 req vpost -> Prop
    := of_expanded2I
    (* changing [sel1_t] into a tuple *)
    (sel1_tu   : list Type)
    (sel1_tu_f : sel1_t e -> Tuple.t sel1_tu)
    (sel1_tu_g : Tuple.t sel1_tu -> sel1_t e)
    (sel1_TU   : Tuple.type_iso_tu (sel1_t e) sel1_tu sel1_tu_f sel1_tu_g)
    (sel1_TU_GOAL : forall sel1 : sel1_t e,
      Tuple.type_iso_tu_goal (e sel1) _ sel1_TU)
    (* the vprops of [post] must be independents of [sel1] *)
    (VPOST : Tuple.arrow sel1_tu (fun sel1' =>
      let sel1 : sel1_t e := sel1_tu_g sel1' in
      forall REQ : req,
      VpropList.of_ctx (post (e sel1 REQ)) = vpost))
    (vs1 : Tuple.arrow sel1_tu (fun _ => req -> Spec.t_vs1 vpost))
    (VS1 : Tuple.arrow sel1_tu (fun sel1' =>
      let sel1 : sel1_t e := sel1_tu_g sel1' in
      forall REQ : req,
      of_expanded3 (e sel1 REQ)
        (eq_rect_r Spec.t_vs1 (Tuple.to_fun vs1 sel1' REQ)
                   (Tuple.to_fun VPOST sel1' REQ)))):
    of_expanded2 e (@Spec.mk_vs0 req vpost sel1_tu vs1).

  Inductive of_expanded1 (e : Expanded.t_r1) : Spec.t_r1 Spec.t_vs -> Prop
    := of_expanded1I
    (vpost : opt_sigG GO -> VpropList.t)
    (val   : forall xG : opt_sigG GO, Spec.t_vs0 (req e) (vpost xG))
    (VAL   : forall xG : opt_sigG GO, of_expanded2 (e xG) (val xG)):
    of_expanded1 e (Spec.mk_r1 _ (prs e) (pre e) vpost (Spec.mk_vs (req e) val)).

  Inductive of_expanded0 (e : Expanded.t_r0) : Spec.t_r0 Spec.t_vs -> Prop
    := of_expanded0I
    (s1 : sel0_t e -> Spec.t_r1 Spec.t_vs)
    (S1 : forall sel0 : sel0_t e, of_expanded1 (e sel0) (s1 sel0)):
    of_expanded0 e (Spec.mk_r0 (sel0_t e) s1).

  Definition of_expanded (e : Expanded.t) (s : Spec.t GI A GO) : Prop :=
    forall gi : ghin_t GI, of_expanded0 (e gi) (s gi).

  (* We prove that [of_expanded] builds an equivalent specification: *)

  Lemma of_expanded2_equiv [req] e vpost s REQ
    (E : @of_expanded2 req e vpost s):
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
      set (x_VS1 := Tuple.to_fun VS1 sel1' REQ); clearbody x_VS1; clear VS1.
      set (x_vs1 := Tuple.to_fun vs1 sel1' REQ) in *.
        simpl in x_vs1, x_VS1; fold x_vs1 in x_VS1; clearbody x_vs1; clear vs1.
      set (x_VPOST := Tuple.to_fun VPOST sel1' REQ) in *; clearbody x_VPOST; clear VPOST.
      destruct x_VPOST; cbn in *.
      case x_VS1; unfold Spec.post; cbn.
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
    case (S1 sel0) as [vpost val VAL]; cbn.
    setoid_rewrite (fun REQ xG => of_expanded2_equiv REQ (VAL xG)).
    reflexivity.
  Qed.
End Expanded. End Expanded.
  Global Arguments t          : clear implicits.
  Global Arguments t'         : clear implicits.
  Global Arguments mk_r1 [A GO p_val].
  Global Arguments Expanded.t : clear implicits.
  Global Arguments Expanded.mk_r1 [A] [GO].

  (* The semantics of [Spec.t] is equivalent to the one induced by [to_expanded] *)
  Lemma tr_eq_expanded [GI A GO] (vs : t GI A GO) (ss : SP.Spec.t A):
    Spec.tr vs ss <-> Expanded.tr (Expanded.to_expanded vs) ss.
  Proof.
    apply Morphisms_Prop.ex_iff_morphism; intro gi.
    apply Morphisms_Prop.ex_iff_morphism; intro sel0.
    unfold sem_pt_ex.
    split.
    - intros (pt & (REQ & POST) & H).
      exists REQ.
      etransitivity; [clear H|exact H].
      split; cbn.
      + reflexivity.
      + intro x; SL.normalize.
        Intro go; Apply go.
        unfold Expanded.tr_post; SL.normalize.
        Intro sel1; Intro ENS%POST.
        EApply; Apply ENS.
        reflexivity.
    - intros (REQ & H).
      exists (fun xG spost => let vs := val (vs gi sel0) xG in
         exists sel1 : Tuple.t (Spec.sel1_t vs), let vs := vs sel1 REQ in
           spost = Spec.spost vs /\ Spec.ens vs).
      cbn; split; [|etransitivity; [clear H|exact H]; split].
      + exists REQ; cbn; eauto.
      + reflexivity.
      + intro x; SL.normalize.
        Intro go; Apply go.
        unfold Expanded.tr_post; SL.normalize.
        Intro spost; Intro (sel1 & -> & ENS).
        Apply sel1; Apply ENS.
        reflexivity.
  Qed.
  
  Definition spec_match [GI A GO] (vs : t GI A GO) (ss : SP.Spec.t A -> Prop) : Prop :=
    forall s0, tr vs s0 ->
    exists s1, SP.Spec.le s1 s0 /\ ss s1.
End Spec.

Section F_SPEC.
  (* We need to quantify over the argument to obtain a function specification. *)

  Local Set Implicit Arguments.
  Variable sg : f_sig.

  Record f_sigh := mk_f_sigh {
    f_ghin_t  : option (f_arg_t sg -> Type);
    f_ghout_t : option (f_ret_t sg -> Type);
  }.
  Variable sgh : f_sigh.

  Definition f_ghin_t_x (x : f_arg_t sg) : option Type :=
    option_map (fun gi => gi x) (f_ghin_t sgh).

  Definition f_retgh_t : Type :=
    @Spec.opt_sigG (f_ret_t sg) (f_ghout_t sgh).

  Definition sigh_spec_t' (p_val : Spec.p_val_t (f_ghout_t sgh)) (x : f_arg_t sg) :=
    Spec.t' (f_ghin_t_x x) (f_ret_t sg) (f_ghout_t sgh) p_val.
  Definition sigh_spec_t := sigh_spec_t' Spec.t_vs.

  Definition f_spec' (p_val : Spec.p_val_t (f_ghout_t sgh)) :=
    forall x, sigh_spec_t' p_val x.
  Definition f_spec := f_spec' Spec.t_vs.
  
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

  Definition f_spec_equiv (e : f_spec_exp) (s : f_spec) : Prop :=
    forall x : f_arg_t sg, Spec.Expanded.of_expanded (e x) (s x).

  Record FSpec (e : f_spec_exp) := mk_FSpec {
    m_spec  : f_spec;
    m_equiv : f_spec_equiv e m_spec;
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

  Lemma cp_is_spec_declared (f : fid) (s : f_spec)
    (HSIG : SIG f = Some sg)
    (HSPC : CP.fun_has_spec SPC f HSIG = cp_f_spec s):
    forall x, fun_has_spec f HSIG (s x).
  Proof.
    apply cp_has_spec, HSPC.
  Qed.

  Lemma cp_is_declared (f : fid) (s : f_spec)
    (HSIG : SIG f = Some sg)
    (HSPC : CP.fun_has_spec SPC f HSIG = cp_f_spec s):
    f_declared f s.
  Proof.
    exists HSIG.
    exact (cp_is_spec_declared f HSIG HSPC).
  Defined.

  Record f_decl (s : f_spec) : Type := {
    fd_id : fid;
    fd_H  : f_declared fd_id s;
  }.
End F_SPEC.
Global Arguments FSpec [sg] sgh e.

Section GhostLemma.
  Import Spec.
  Local Set Implicit Arguments.

  (* Lemmas use the same specifications as functions.
     However we do not need the ghost argument and return value since
     the standard ones are already interpreted as ghost. *)
  Variable (sg : f_sig).
  Definition lem_sigh : f_sigh sg := mk_f_sigh _ None None.

  Definition ghost_spec := f_spec lem_sigh.

  (* The semantics of lemmas is an [SLprop.imp]. *)
  Definition ghost_lem (s : ghost_spec) : Prop :=
    forall (x    : f_arg_t    sg), let s  := s x tt in
    forall (sel0 : Spec.sel0_t s), let s0 := s sel0 in let sv := Spec.val s0 in
    forall REQ : Spec.req sv,
    SLprop.imp
      (CTX.sl (Spec.pre s0 ++ Spec.prs s0))
      (SLprop.ex (f_ret_t sg) (fun res => let sv := sv res  in
       SLprop.ex (Tuple.t (Spec.sel1_t sv)) (fun sel1 => let sv := sv sel1 REQ in
       SLprop.pure (Spec.ens sv) **
       CTX.sl (Spec.post sv ++ Spec.prs s0))))%slprop.
End GhostLemma.

Section VProg.

(* A vprog instruction [i : instr A] contains a concrete program [i_impl i].
   Given an initial context [ctx], we build using the [build_HasSpec] tactic an equivalent
   functional program [f].
   When building [HasSpec i ctx s f], we also infer:
   - The subset of consumed vprops of [ctx]: [sf_csm s].
     The complementary subset of vprops of [ctx] are preserved, that is, they appear in the
     postcondition with the same selector.
   - A list of produced vprops: [sf_prd s].
     The functional specification [f] returns their selectors.
 *)

(* [i_spec_t] *)

(* [i_sig_t] *)

Local Set Implicit Arguments.
Record i_sig_t (A : Type) (ctx : CTX.t) := mk_i_sig {
  sf_csm : Sub.t ctx;
  sf_prd : A -> VpropList.t;
}.
Local Unset Implicit Arguments.
Global Arguments mk_i_sig [A ctx] _ _.

Section GETTERS.
  Context [A ctx] (s : i_sig_t A ctx).

  Definition sf_rsel (x : A) : list Type :=
    VpropList.sel (sf_prd s x).

  Definition sf_rvar : TF.p :=
    TF.mk_p A (sf_prd s).
  
  Definition sf_rvar_t : Type :=
    TF.t sf_rvar.

  Definition sf_prd_ctx (r : sf_rvar_t) : CTX.t :=
    VpropList.inst (sf_prd s (TF.v_val r)) (TF.v_sel r).

  Definition sf_post_ctx (r : sf_rvar_t) : CTX.t :=
    sf_prd_ctx r ++ CTX.sub ctx (Sub.neg (sf_csm s)).

  Definition sf_post (post : sf_rvar_t -> Prop) (x : A) : SLprop.t :=
    SLprop.ex (VpropList.sel_t (sf_prd s x)) (fun sels =>
      let r := TF.mk (sf_prd s) x sels in
      SLprop.pure (post r) **
      CTX.sl (sf_post_ctx r))%slprop.
End GETTERS.
Global Arguments sf_rsel _ _ !_/.
Global Arguments sf_rvar _ _ !_/.
Global Arguments sf_rvar_t _ _ !_/.
Global Arguments sf_prd_ctx _ _ !_ !_/.
Global Arguments sf_post_ctx _ _ !_ !_/.
Global Arguments sf_post _ _ !_ _/.

(* [i_spec_t] *)
Definition i_spec_t [A ctx] (sg : i_sig_t A ctx) :=
  FP.instr (sf_rvar sg).

(* [instr] *)

  Context (CT : CP.context).
  Let SIG : sig_context         := projT1 CT.
  Let SPC : CP.spec_context SIG := projT2 CT.

Definition sound_spec [A : Type] (i : @CP.instr SIG A) (ctx : CTX.t)
    (s : i_sig_t A ctx) (f : i_spec_t s) : Prop :=
  forall (post : sf_rvar_t s -> Prop)
         (PRE : FP.wlp f post),
  SP.sls SPC i {|
    SP.Spec.pre  := CTX.sl ctx;
    SP.Spec.post := sf_post s post;
  |}.

Definition i_spec_p [A : Type] (i : @CP.instr SIG A) (ctx : CTX.t) : Type :=
  { sp : forall s : i_sig_t A ctx, i_spec_t s -> Prop
       | forall s f (SP : sp s f), sound_spec i ctx s f }.

Local Set Implicit Arguments.
Record instr (A : Type) := mk_instr {
  (* underlying concrete program *)
  i_impl : @CP.instr SIG A;
  (* a predicate to build a functional specification *)
  i_spec : forall ctx : CTX.t, i_spec_p i_impl ctx;
}.
Local Unset Implicit Arguments.

Inductive HasSpec [A : Type] (i : instr A) (ctx : CTX.t) (s : i_sig_t A ctx) (f : i_spec_t s) : Prop :=
  HasSpecI (S : sound_spec (i_impl i) ctx s f).

Lemma HasSpec_ct [A i ctx s f]
  (C : proj1_sig (i_spec i ctx) s f):
  @HasSpec A i ctx s f.
Proof.
  constructor; apply (proj2_sig (i_spec i ctx) s), C.
Qed.

(* Transformation *)

(* [TrSpecH s0 s1 F] means that any instruction that admits [s0, f0] as specification also admits [s1, F f0]. *)
Definition TrSpecH [A : Type] [ctx0 ctx1 : CTX.t]
  (s0 : i_sig_t A ctx0) (s1 : i_sig_t A ctx1) (F : i_spec_t s0 -> i_spec_t s1) : Prop :=
  forall (i : @CP.instr SIG A) (f0 : i_spec_t s0)
    (S0 : sound_spec i ctx0 s0 f0), sound_spec i ctx1 s1 (F f0).

Inductive TrSpec [A : Type] [ctx : CTX.t] (s0 s1 : i_sig_t A ctx) (F : i_spec_t s0 -> i_spec_t s1): Prop :=
  TrSpecI (T : TrSpecH s0 s1 F).

Lemma TrSpecH_refl [A ctx] s:
  @TrSpecH A ctx ctx s s (fun f => f).
Proof.
  intros ? ? S0. exact S0.
Qed.

Lemma TrSpecH_trans [A ctx0 ctx1 ctx2 s0 s1 s2 F0 F1]
  (T0 : @TrSpecH A ctx0 ctx1 s0 s1 F0)
  (T1 : @TrSpecH A ctx1 ctx2 s1 s2 F1):
  @TrSpecH A ctx0 ctx2 s0 s2 (fun f => F1 (F0 f)).
Proof.
  intros i f S0.
  apply T1, T0, S0.
Qed.

Lemma transform_spec [A ctx i s0 s1 F f]
  (H : HasSpec i ctx s0 f)
  (T : TrSpec s0 s1 F):
  @HasSpec A i ctx s1 (F f).
Proof.
  constructor; apply T, H.
Qed.

(* equality between signatures and an [eq_ind] for the specification *)
Inductive i_sig_eq
  [ctxn : nat] [A : Type] [FT : forall prd1 : A -> VpropList.t, Type]
  (csm0 : Vector.t bool ctxn) (prd0 : A -> VpropList.t) (F0 : FT prd0): forall
  (csm1 : Vector.t bool ctxn) (prd1 : A -> VpropList.t) (F1 : FT prd1), Prop :=
  i_sig_eq_refl :
    i_sig_eq csm0 prd0 F0 csm0 prd0 F0.


Section AddCsm.
  Context [A : Type] [ctx : CTX.t] (s : i_sig_t A ctx) (csm : Sub.t ctx).
  
  Let acsm := CTX.sub ctx (Sub.minus csm (sf_csm s)).

  Definition add_csm : i_sig_t A ctx := {|
    sf_csm  := Sub.or (sf_csm s) csm;
    sf_prd  := fun x => sf_prd s x ++ VpropList.of_ctx acsm;
  |}.

  Definition add_csm_f (f : i_spec_t s) : i_spec_t add_csm :=
    FunProg.Bind f (TF.of_fun (T:=sf_rvar s) (fun x =>
    FunProg.Ret (TF.mk _ (TF.v_val x) (VpropList.app_sel (TF.v_sel x) (VpropList.sel_of_ctx acsm))))).

  Local Opaque TF.to_fun TF.of_fun.

  Lemma Tr_add_csm:
    TrSpec s add_csm add_csm_f.
  Proof.
    constructor.
    intros i f S0 post PRE; simpl in PRE.
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
Global Arguments add_csm   _ _ !s !csm.
Global Arguments add_csm_f _ _ !s !csm f/.

Section ChangePrd.
  Context [A : Type] [ctx : CTX.t] (s : i_sig_t A ctx)
          (prd : A -> VpropList.t).

  Definition change_prd : i_sig_t A ctx := {|
    sf_csm  := sf_csm s;
    sf_prd  := prd;
  |}.
  
  Variables (rsel : forall r : sf_rvar_t s, VpropList.sel_t (prd (TF.v_val r)))
            (RSEL : forall r : sf_rvar_t s,
                    CTX.Trf.t (sf_prd_ctx s r)
                              (VpropList.inst (prd (TF.v_val r)) (rsel r))).

  Definition change_prd_f (f : i_spec_t s) : i_spec_t change_prd :=
    FunProg.Bind f (TF.of_fun (T:=sf_rvar s) (fun r =>
    FunProg.Ret (TF.mk _ (TF.v_val r) (rsel r)))).

  Local Opaque TF.to_fun TF.of_fun.

  Lemma Tr_change_prd:
    TrSpec s change_prd change_prd_f.
  Proof.
    constructor.
    intros i f S post PRE.
    eapply SP.Cons.
      { apply S, PRE. }
    clear S PRE.
    split. reflexivity.
    unfold sf_post, sf_post_ctx; cbn.
    intro x.
    Intro sel.
    Apply (rsel (TF.mk _ x sel)).
    rewrite TF.to_of_fun.
    cbn; rewrite !CTX.sl_app, !TF.to_of_tu.
    apply SLprop.star_morph_imp. reflexivity.
    apply SLprop.star_morph_imp. 2:reflexivity.
    refine (CTX.Trf.t_fwd (RSEL _)).
  Qed.
End ChangePrd.
Global Arguments change_prd   _ _ !s prd.
Global Arguments change_prd_f _ _ !s prd rsel f/.

Lemma Tr_change_exact [A ctx s csm1 prd1 F]:
  let s1 := add_csm s csm1 in forall
  (rsel : TF.arrow (sf_rvar s1) (fun r => VpropList.sel_t (prd1 (TF.v_val r))))
  (RSEL : TF.arrow (sf_rvar s1) (fun r =>
          CTX.Trf.t (sf_prd_ctx s1 r)
                    (VpropList.inst (prd1 (TF.v_val r)) (TF.to_fun rsel r))))
  (E : i_sig_eq (FT := fun prd1 => i_spec_t s -> FP.instr (TF.mk_p A prd1))
          (sf_csm s1) prd1
          (fun f => change_prd_f s1 prd1 (TF.to_fun rsel) (add_csm_f s csm1 f))
          csm1 prd1 F),
  @TrSpec A ctx s (mk_i_sig csm1 prd1) F.
Proof.
  intros; destruct E.
  constructor; apply TrSpecH_trans.
  - apply Tr_add_csm.
  - apply (Tr_change_prd (add_csm s csm1) prd1 _ (TF.to_fun RSEL)).
Qed.

Section AddFrame.
  Context [A : Type] [ctx : CTX.t] (s : i_sig_t A ctx) (frame : CTX.t).

  Definition add_frame : i_sig_t A (ctx ++ frame) := {|
    sf_csm  := Sub.app (sf_csm s) (Sub.const frame false);
    sf_prd  := sf_prd s
  |}.

  Lemma Tr_add_frame:
    TrSpecH s add_frame (fun f => f).
  Proof.
    intros i f S0 post WLP.
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
Global Arguments add_frame _ _ !s !frame.

Section InjPre.
  Context (m : CTX.t) (ctx : CTX.t).

  Section Full.
    Context (add : CTX.t) [A] (s : i_sig_t A (m ++ add)).

    Inductive InjPre_Spec : forall s' : i_sig_t A ctx, (i_spec_t s -> i_spec_t s') -> Prop
      := InjPre_SpecI
      (rev_f : CTX.Trf.rev_f_t ctx (m ++ add))
      (ij : CTX.Trf.inj_p ctx m add rev_f)
      [csm' prd' F]
      (E  : let (ncsm, rem) := rev_f (Sub.neg (sf_csm s)) in
            i_sig_eq (FT := fun prd1 => i_spec_t s -> FP.instr (TF.mk_p A prd1))
              (Sub.neg ncsm) (fun x : A => sf_prd s x ++ VpropList.of_ctx rem)
              (fun f =>
               FunProg.Bind f (TF.of_fun (T := sf_rvar s) (fun r =>
               FunProg.Ret (TF.mk _ (TF.v_val r) (VpropList.app_sel (TF.v_sel r) (VpropList.sel_of_ctx rem))))))
              csm' prd' F):
      InjPre_Spec (mk_i_sig csm' prd') F.

    Local Opaque DTuple.to_fun.
    Local Set Implicit Arguments.

    Lemma Tr_InjPre [s' F] (SP : InjPre_Spec s' F):
      TrSpecH s s' F.
    Proof.
      case SP as [rev_f [FWD BWD] csm' prd' F E].
      specialize (BWD (Sub.neg (sf_csm s)));
        destruct rev_f as (ncsm, rem) in BWD, E;
        cbn in BWD; rewrite <-!CTX.sl_sub_eq in BWD.
      destruct E.
      intros i f S0 post WLP; cbn in post, WLP.
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
    Context [A] (s : i_sig_t A m) (s' : i_sig_t A ctx) (F : i_spec_t s -> i_spec_t s').

    Inductive InjPre_Frame_Spec : Prop
      := InjPre_Frame_SpecI
      (frame : CTX.t)
      (ij : InjPre_Spec frame (add_frame s frame) s' F).

    Local Set Implicit Arguments.

    Lemma Tr_InjPre_Frame (SP : InjPre_Frame_Spec):
      TrSpecH s s' F.
    Proof.
      case SP as [frame ij].
      intros i f S0.
      eapply (Tr_InjPre ij), Tr_add_frame, S0.
    Qed.
  End Frame.
  Section SFrame.
    Context [A] (s : i_sig_t A m) (f : i_spec_t s).

    Inductive InjPre_SFrame_Spec : forall s' : i_sig_t A ctx, i_spec_t s' -> Prop
      := InjPre_SFrame_SpecI
      (frame : CTX.t)
      (rev_f : CTX.Trf.rev_f_t ctx (m ++ frame))
      (ij : CTX.Trf.inj_p ctx m frame rev_f)
      [csm' prd' f']
      (E  : let s := add_frame s frame in
            let (ncsm, rem) := rev_f (Sub.neg (sf_csm s)) in
            i_sig_eq (FT := fun prd1 => FP.instr (TF.mk_p A prd1))
              (Sub.neg ncsm) (fun x : A => sf_prd s x ++ VpropList.of_ctx rem)
              (FunProg.Bind f (TF.of_fun (T := sf_rvar s) (fun r =>
               FunProg.Ret (TF.mk _ (TF.v_val r) (VpropList.app_sel (TF.v_sel r) (VpropList.sel_of_ctx rem))))))
              csm' prd' f'):
      InjPre_SFrame_Spec (mk_i_sig csm' prd') f'.

    Local Set Implicit Arguments.

    Lemma Tr_InjPre_SFrame [s' f'] (SP : InjPre_SFrame_Spec s' f') [i]:
      sound_spec i m s f -> sound_spec i ctx s' f'.
    Proof.
      destruct SP.
      Tac.set_hyp_let E s0.
      case (rev_f _) as (ncsm, rem) eqn:Rev in E.
      destruct E.
      eassert (InjPre_Frame_Spec s _ _) as IJ. {
        exists frame, rev_f; auto.
        fold s0; rewrite Rev.
        split.
      }
      apply Tr_InjPre_Frame in IJ.
      apply IJ.
    Qed.
  End SFrame.
End InjPre.

(* Function definition *)

Section FunImpl.
  Context [GI : option Type] [A : Type] [GO : option (A -> Type)].
  Let AG := Spec.opt_sigG GO.

  Definition f_body1 : Type :=
    OptTy.arrow GI (fun gi => instr AG).

  Import Spec.

  Definition impl_match_0 [p_val] (sem : Spec.p_val_f p_val)
      (impl : @CP.instr SIG AG) (spec : @Spec.t_r0 A GO p_val) : Prop :=
    forall ss : SP.Spec.t AG,
    tr_0 sem sem_pt_id spec ss ->
    SP.sls SPC impl ss.

  Variables (body : f_body1) (spec : Spec.t GI A GO).

  Definition impl_match :=
    forall (gi : ghin_t GI), impl_match_0 sem_vs (i_impl (OptTy.to_fun' body gi)) (spec gi).

  (* Given a functional representation [f] of an implementation [body] of a function,
     we can prove the correctness of [body] with respect to some specification [spec]
     using the WLP of [f]. *)
  Lemma intro_impl_match
    (H : forall (gi : ghin_t GI) (sel0 : Spec.sel0_t (spec gi)) (REQ : Spec.req (val (spec gi sel0))),
         let ctx : CTX.t := Spec.pre (spec gi sel0) ++ Spec.prs (spec gi sel0) in
         exists (s : i_sig_t AG ctx) (f : i_spec_t s),
         sf_csm s = Sub.const ctx true /\
         sound_spec (i_impl (OptTy.to_fun' body gi)) ctx s f /\
         FP.wlp f (fun r =>
           let xG     := TF.v_val r in
           let f_post := VpropList.inst (sf_prd s (TF.v_val r)) (TF.v_sel r) in
           exists sel1 : Tuple.t (Spec.sel1_t (val (spec gi sel0) xG)),
           SLprop.imp (CTX.sl f_post)
                      (CTX.sl (Spec.post (val (spec gi sel0) xG sel1 REQ) ++ Spec.prs (spec gi sel0))) /\
           Spec.ens (val (spec gi sel0) xG sel1 REQ)
         )):
    impl_match.
  Proof.
    intros gi ss (sel0 & pt & (REQ & POST) & LE).
    case (H gi sel0 REQ) as (s & f & F_CSM & F_SPEC & WLP); clear H.
    eapply SP.Cons.
      { apply F_SPEC, WLP. }
    rewrite <- LE.
    clear LE F_SPEC WLP.
    unfold sf_post, sf_post_ctx, sem_pt_id; split; cbn.
    - rewrite CTX.sl_app; reflexivity.
    - intro xG.
      Intro rsel.
      Intro (sel1 & IMP & ENS%POST).
      unfold Expanded.tr_post; cbn; SL.normalize.
      EApply; Apply ENS.
      rewrite F_CSM; unfold Sub.neg, Sub.const;
        rewrite Vector.map_const, Sub.sub_const_false, app_nil_r.
      rewrite CTX.sl_app in IMP; exact IMP.
  Qed.

  Section Impl_Match.
    Variables (body_1 : instr AG) (s_1 : @Spec.t_r1 A GO t_vs).

  Let s_post (xG : AG) (sel1 : Tuple.t (Spec.sel1_t (val s_1 xG))) (REQ : Spec.req (val s_1)) :=
    Spec.post (val s_1 xG sel1 REQ) ++ Spec.prs s_1.
  Let s_vpost (xG : AG) :=
    Spec.vpost s_1 xG ++ VpropList.of_ctx (Spec.prs s_1).
  Let rvar :=
    TF.mk_p AG s_vpost.

  Local Lemma s_vpost_eq (xG : AG) (sel1 : Tuple.t (Spec.sel1_t (val s_1 xG))) (REQ : Spec.req (val s_1)):
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
      (F : HasSpec body_1 ctx (mk_i_sig (Sub.const ctx true) s_vpost) f)
      (* simplification of the existential quantification on sel1.
         Maybe we could expend the wlp of add_csm to remove the equalities on
         non consumed vprops ? *)
      (ex_sel1 : forall (x : AG) (REQ : Spec.req (val s_1)) (P : Tuple.t (Spec.sel1_t (val s_1 x)) -> Prop),
              Tuple.arrow (VpropList.sel (s_vpost x)) (fun _ => Prop))
      (EX_SEL1 : forall (x : AG) (REQ : Spec.req (val s_1)) (P : Tuple.t (Spec.sel1_t (val s_1 x)) -> Prop),
              Tuple.arrow (VpropList.sel (s_vpost x)) (fun rsel =>
              Tuple.ex (sel1_t (val s_1 x)) (fun sel1 =>
              Tuple.typed_eq (VpropList.sel_of_ctx (s_post x sel1 REQ))
                             (eq_rect_r VpropList.sel_t rsel (s_vpost_eq x sel1 REQ)) /\
              P sel1) <-> Tuple.to_fun (ex_sel1 x REQ P) rsel))
      (* VC *)
      (WLP : forall REQ : Spec.req (val s_1),
             FunProg.wlpA f (TF.of_fun (T := rvar) (fun r =>
               let x := TF.v_val r in
               Tuple.to_fun (ex_sel1 x REQ (fun sel1 => Spec.ens (val s_1 x sel1 REQ))) (TF.v_sel r)))),
      Impl_Match.
  End Impl_Match.

  Lemma intro_impl_match1
    (H : forall gi sel0, Impl_Match (OptTy.to_fun' body gi) (spec gi sel0)):
    impl_match.
  Proof.
    apply intro_impl_match.
    intros gi sel0 REQ ctx.
    destruct (H gi sel0); clear H.
    do 2 eexists. split. 2:split.
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
      reflexivity.
  Qed.
End FunImpl.

Section FunImplBody.
  (* [f_ebody] encapsulates an implementation with a signature [f_body] that includes the ghost
     argument and result (if any) into an implementation with a signature [CP.f_impl] that does
     not mention them.
     This is achieved by introducing the ghost argument using [Oracle] and dropping the ghost result.
   *)

  Local Set Implicit Arguments.
  Variables (sg : f_sig) (sgh : f_sigh sg).

  Definition f_body : Type :=
    forall (x : f_arg_t sg), @f_body1 (f_ghin_t_x sgh x) (f_ret_t sg) (f_ghout_t sgh).

  Variable (impl : f_body).

  Definition f_body_match (spec : f_spec sgh) : Prop :=
    forall x : f_arg_t sg, impl_match (impl x) (spec x).

  Definition f_ebody : @CP.f_impl SIG sg.
  Proof.
    assert (prj : f_retgh_t sgh -> @CP.instr SIG (f_ret_t sg)). {
      intro x; apply CP.Ret; revert x.
      unfold f_retgh_t; case f_ghout_t as [GO|].
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
    intros arg s (gi & sel0 & pt & SEM & LE).
    do 2 esplit; [exact LE|clear LE].
    cbv delta [f_ebody].
    set (prj := fun x => CP.Ret _).
    eenough _ as PRJ. clearbody prj.
    - cbn.
      unfold Spec.sem_pt_ex, f_body, f_body_match, impl_match,
        f_spec, f_spec', sigh_spec_t, sigh_spec_t', f_ghin_t_x in *.
      destruct f_ghin_t; cbn in *.
      + eapply SP.Bind.
        { apply SP.Oracle with (x := gi). }
        intro; apply SP.PureE; intros ->.
        eapply SP.Bind.
        { apply M.
          exists sel0, pt.
          split. exact SEM. reflexivity. }
        cbn. exact PRJ.
      + destruct gi.
        eapply SP.Bind.
        { apply (@M arg tt).
          exists sel0, pt.
          split. exact SEM. reflexivity. }
        exact PRJ.
    - subst prj; clear.
      unfold Spec.sem_pt_id, f_spec, f_spec', sigh_spec_t, sigh_spec_t' in *.
      destruct f_ghout_t; cbn in *.
      + intros [res go]; SL.normalize.
        apply SP.CRet.
        Apply go.
        reflexivity.
      + intro res; SL.normalize.
        apply SP.CRet.
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

  Definition f_erase : Type :=
    { i : @CP.f_impl SIG sg | forall x : f_arg_t sg, CP.erase (f_ebody x) (i x) }.

  Variable (i : f_erase).

  Lemma f_erase_match_spec:
    CP.f_match_spec SPC (proj1_sig i) (cp_f_spec spec).
  Proof.
    intros arg s S m0 PRE.
    apply (proj2_sig i arg), f_ebody_match_spec; assumption.
  Qed.

  Lemma f_erase_oracle_free:
    forall x : f_arg_t sg, CP.oracle_free (proj1_sig i x).
  Proof.
    intro; apply (proj2_sig i x).
  Qed.
End FunImplBody.

(* Fragment *)

Section Fragment.
  (* A fragment is similar to a function but it is inlined and has no corresponding concrete
     function. *)
  Local Set Implicit Arguments.
  Variables (sg : f_sig) (sgh : f_sigh sg).

  Definition frag_impl : Type :=
    forall (x : f_arg_t sg) (gi : OptTy.t (f_ghin_t_x sgh x)),
    @CP.instr SIG (f_retgh_t sgh).

  Definition frag_correct [p_val] (sem : Spec.p_val_f p_val) (impl : frag_impl) (spec : f_spec' sgh p_val) :=
    forall (x : f_arg_t sg) (gi : OptTy.t (f_ghin_t_x sgh x)),
    impl_match_0 sem (impl x gi) (spec x gi).

  Lemma impl_match_frag_correct [impl : f_body sgh] [spec : f_spec sgh]
    (H : forall x : f_arg_t sg, impl_match (impl x) (spec x)):
    frag_correct Spec.sem_vs (fun x gi => i_impl (OptTy.to_fun' (impl x) gi)) spec.
  Proof. exact H. Qed.
End Fragment.
Section Frag_correct_wrapper.
  (* A wrapper [Frag_correct] around (and convertible to) [frag_correct] *)

  Import Spec.

  Context
    (arg_t : Type) (ghin_t  : option (arg_t -> Type))
    (res_t : Type) (ghout_t : option (res_t -> Type))
    [p_val : Spec.p_val_t ghout_t] (sem : Spec.p_val_f p_val)
    (frag  : forall x : arg_t, OptTy.t (option_map (B := Type) (fun gi : arg_t -> Type => gi x) ghin_t) ->
             @CP.instr (projT1 CT) (Spec.opt_sigG ghout_t) * Spec.t_r0 p_val).
             (* NOTE (coqc 8.16.1): the extra annotations are necessary for universes *)

  Definition Frag_correct
    : Prop
    := @frag_correct _ (mk_f_sigh (mk_f_sig arg_t res_t) ghin_t ghout_t) p_val sem
          (fun x gi => fst (frag x gi)) (fun x gi => snd (frag x gi)).

  Lemma intro_Frag_correct
    (H : forall (x : arg_t) (gi : OptTy.t (option_map (B := Type) (fun gi : arg_t -> Type => gi x) ghin_t)),
         let s := snd (frag x gi) in
         forall (sel0 : Spec.sel0_t s),
         let s := s sel0 in
         forall (pt : Spec.val_pt (Spec.vpost s)) (SEM : sem _ (Spec.val s) pt),
         SP.sls (projT2 CT) (fst (frag x gi)) {|
           SP.Spec.pre  :=
             CTX.sl (Spec.pre s) ** CTX.sl (Spec.prs s);
           SP.Spec.post := fun xG : Spec.opt_sigG ghout_t =>
             SLprop.ex (VpropList.sel_t (Spec.vpost s xG)) (fun sel1 =>
             SLprop.pure (pt xG sel1) **
             CTX.sl (VpropList.inst (Spec.vpost s xG) sel1) **
             CTX.sl (Spec.prs s))%slprop
         |}):
    Frag_correct.
  Proof.
    unfold Frag_correct, frag_correct, impl_match_0, Spec.tr_0, Spec.sem_pt_id; cbn.
    intros x gi ss (sel0 & pt & SEM & LE).
    eapply SP.Cons.
    exact (H x gi sel0 pt SEM).
    rewrite <- LE.
    split; intros; SL.normalize; reflexivity.
  Qed.
End Frag_correct_wrapper.


(* Constructors *)

Section Ret.
  Section Impl.
    Context [A : Type] (x : A).

    Definition no_pt_hint : VpropList.t.
    Proof. exact nil. Qed.

    Inductive Ret_Spec (pt_hint : A -> VpropList.t) (ctx : CTX.t) (s : i_sig_t A ctx) (f : i_spec_t s): Prop
      := Ret_SpecI
      (pt : A -> VpropList.t)
      (sels : Tuple.t (map Vprop.ty (pt x)))
      (IJ :
        let pre := VpropList.inst (pt x) sels in
        InjPre_SFrame_Spec pre ctx {|
          sf_csm  := Sub.const pre true;
          sf_prd  := pt;
        |} (FunProg.Ret (TF.mk pt x sels)) s f).

    Program Definition Ret0 pt_hint : instr A := {|
      i_impl := CP.Ret x;
      i_spec := fun ctx => Ret_Spec pt_hint ctx;
    |}.
    Next Obligation.
      destruct SP; apply (Tr_InjPre_SFrame IJ).
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

  Definition Ret [A : Type] (x : A) {pt : opt_arg (A -> list Vprop.t) (fun _ => no_pt_hint)}
    : instr A
    := Ret0 x pt.

  Definition RetG [A : Type] [P : A -> Type] (x : A) (y : P x)
      {pt : opt_arg (forall x : A, P x -> list Vprop.t) (fun _ _ => no_pt_hint)}
    : instr (CP.sigG A P)
    := Ret0 (CP.existG P x y) (CP.split_sigG pt).
End Ret.
Section Bind.
  Context [A B : Type] (f : instr A) (g : A -> instr B).

  Section Spec1.
    Variables (ctx : CTX.t) (s_f : i_sig_t A ctx) (r : sf_rvar_t s_f).

    Inductive Bind_Spec1:
      forall s : i_sig_t B ctx(* bind sig *), FP.instr (TF.mk_p B (sf_prd s)) (* g spec *) -> Prop
      := Bind_SpecI1
      [s_g : i_sig_t B (sf_post_ctx s_f r)] [f_g : i_spec_t s_g]
      (S_G : HasSpec (g (TF.v_val r)) (sf_post_ctx s_f r) s_g f_g)
      [b_csm b_prd F]
      (E :
        let f_prd : Sub.t (sf_post_ctx s_f r) :=
            Sub.app (Sub.const (sf_prd_ctx s_f r) true)
                    (Sub.const (CTX.sub ctx (Sub.neg (sf_csm s_f))) false) in
        let s_g' : i_sig_t B (sf_post_ctx s_f r) := add_csm s_g f_prd in
        i_sig_eq (FT := fun prd => i_spec_t s_g -> FP.instr (TF.mk_p B prd))
             (Sub.pull (sf_csm s_f)
                (Sub.const (Sub.sub ctx (sf_csm s_f)) true)
                (snd (Sub.split
                        (VpropList.inst (sf_prd s_f (TF.v_val r)) (TF.v_sel r))
                        (CTX.sub ctx (Sub.neg (sf_csm s_f)))
                        (sf_csm s_g'))))
             (sf_prd s_g')
             (add_csm_f s_g f_prd)
             b_csm b_prd F):
      Bind_Spec1 (mk_i_sig b_csm b_prd) (F f_g).

    Lemma Bind_Spec1_correct s f_g
      (H : Bind_Spec1 s f_g)
      post (PRE : FP.wlp f_g post):
      SP.sls SPC (i_impl (g (TF.v_val r))) {|
        SP.Spec.pre  := CTX.sl (sf_post_ctx s_f r);
        SP.Spec.post := sf_post s post;
      |}.
    Proof.
      destruct H.
      Tac.set_hyp_let E f_prd.
      Tac.set_hyp_let E s_g'.
      destruct E.
      cbn in post, PRE.
      eapply transform_spec in S_G.
        2:{ apply Tr_add_csm with (csm := f_prd). }
      eapply SP.Cons.
        { apply S_G, PRE. }
      clear PRE S_G.
      split; unfold sf_post; cbn.
      - reflexivity.
      - intro y.
        change (add_csm _ _) with s_g'.
        Intro sel2. Intro POST.
        Apply sel2. Apply POST.
        clear.
        unfold sf_post_ctx, sf_prd_ctx in *; cbn.
        rewrite !CTX.sl_app.
          apply SLprop.star_morph_imp. reflexivity.
        assert (exists csm, sf_csm s_g' = Sub.app (Sub.const _ true) csm) as [g_csm ->]. {
          exists (snd (Sub.split _ _ (sf_csm s_g'))).
          unfold s_g', f_prd, add_csm; cbn; clear.
          rewrite (Sub.app_split _ _ (sf_csm s_g)).
            case (Sub.split _ _ (sf_csm s_g)) as [g_csm0 g_csm1]; cbn.
          unfold Sub.const, Sub.or.
          etransitivity. apply Sub.map2_app.
          f_equal.
          - apply Vector.ext; intro k;
            erewrite Vector.nth_map2, !Vector.const_nth by reflexivity;
            destruct (Vector.nth _ k); reflexivity.
          - symmetry.
            eassert (Vector.map2 _ _ _ = _) as -> by apply Sub.map2_app.
            rewrite Sub.split_app; cbn.
            reflexivity.
        }
        clearbody f_prd s_g'.
        unfold Sub.neg, Sub.const.
        rewrite Sub.map_app, Sub.sub_app, Sub.split_app, Sub.map_pull,
                Sub.sl_pull, !Vector.map_const, !Sub.sub_const_false;
        SL.normalize.
        reflexivity.
    Qed.
  End Spec1.

  Inductive Bind_Spec (ctx : CTX.t) (s : i_sig_t B ctx): i_spec_t s -> Prop
    := Bind_SpecI
    [s_f : i_sig_t A ctx] [f_f : i_spec_t s_f]
    (S_F : HasSpec f ctx s_f f_f)
    [f_g : TF.arrow (sf_rvar s_f) (fun _ => FP.instr (TF.mk_p B (sf_prd s)))]
    (S_1 : TF.arrow (sf_rvar s_f) (fun r => Bind_Spec1 ctx s_f r s (TF.to_fun f_g r))):
    Bind_Spec ctx s (FunProg.Bind f_f f_g).



  Program Definition Bind : instr B := {|
    i_impl := CP.Bind (i_impl f) (fun x => i_impl (g x));
    i_spec := fun ctx => Bind_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro.
    eapply SP.Bind.
    - apply S_F, PRE.
    - intro x.
      unfold sf_post.
      apply SP.ExistsE; intro sel1.
        set (r := TF.mk _ x sel1).
      apply SP.PureE.
      eapply Bind_Spec1_correct, (DTuple.to_fun S_1 r).
  Qed.
End Bind.
Section Branch.
  Definition branch_csm_or [ctx : CTX.t] (csms : list (Sub.t ctx)) : Sub.t ctx :=
    List.fold_left (@Sub.or ctx) csms (Sub.const ctx false).

  Lemma TrSpec_branch_0 [A ctx s0 s1_csm s1_prd F] csm
    (E : let s1 := add_csm s0 csm in
         i_sig_eq (FT := fun prd => i_spec_t s0 -> FP.instr (TF.mk_p A prd))
           (sf_csm s1) (sf_prd s1) (add_csm_f s0 csm)
           s1_csm s1_prd F):
    @TrSpec A ctx s0 (mk_i_sig s1_csm s1_prd) F.
  Proof.
    destruct E.
    apply Tr_add_csm.
  Qed.
End Branch.
Section Call.
  Import Spec.
  Section Spec.
    Context [res_t : Type] [ghout_t : option (res_t -> Type)]
            [p_val : p_val_t ghout_t] (sem : Spec.p_val_f p_val)
            (s : @Spec.t_r0 res_t ghout_t p_val).

    Let AG := opt_sigG ghout_t.

    Definition call_f_spec_t : Type :=
      forall sel0 : Spec.sel0_t s, FP.instr (TF.mk_p AG (fun x => Spec.vpost (s sel0) x)).
    Variable f_spec : call_f_spec_t.

    Inductive Call_Spec (ctx : CTX.t) (sg : i_sig_t AG ctx) (f : i_spec_t sg): Prop
      := Call_SpecI
      (sel0 : Spec.sel0_t s):
      let ppre := Spec.pre (s sel0) ++ Spec.prs (s sel0)              in
      let sg0  := {|
        sf_csm  := Sub.app (Sub.const (Spec.pre (s sel0)) true)
                           (Sub.const (Spec.prs (s sel0)) false);
        sf_prd  := fun xG => Spec.vpost (s sel0) xG;
      |} in
      forall
      (IJ : InjPre_SFrame_Spec ppre ctx sg0 (f_spec sel0) sg f),
      Call_Spec ctx sg f.

 
    Definition correct_Call_spec_val [vpost : vpost_t ghout_t] (vs : p_val vpost)
        (repr : FP.instr (TF.mk_p AG vpost)) : Prop :=
      forall (pt : TF.mk_t (opt_sigG ghout_t) vpost -> Prop),
      FunProg.wlp repr pt ->
      sem vpost vs (fun xG sel1 => pt (TF.mk _ xG sel1)).

    Class spec_sem_func := {
      sem_repr : forall (vpost : vpost_t ghout_t) (vs : p_val vpost),
                 FunProg.instr (TF.mk_p (opt_sigG ghout_t) vpost);
      sem_repr_correct :
        forall vpost vs, correct_Call_spec_val vs (sem_repr vpost vs)
    }.

    Definition correct_Call_spec : Prop :=
      forall sel0, correct_Call_spec_val (Spec.val (s sel0)) (f_spec sel0).


    Definition correct_Call_impl (impl : @CP.instr SIG AG) : Prop :=
      forall ss, Spec.tr_0 sem Spec.sem_pt_id s ss ->
      SP.sls SPC impl ss.

    Lemma Call_spec_lem [impl]
      (SPEC : correct_Call_spec)
      (IMPL : correct_Call_impl impl)
      [ctx sg f] (SP : Call_Spec ctx sg f):
      sound_spec impl ctx sg f.
    Proof.
      destruct SP.
      apply (Tr_InjPre_SFrame IJ); clear IJ.
      intros pt WLP; cbn.
      eapply SP.Cons. {
        apply IMPL.
        exists sel0, (fun xG sel1 => pt (TF.mk _ xG sel1)).
        split. 2:reflexivity.
        apply SPEC, WLP.
      }
      split; cbn.
      - unfold ppre; rewrite CTX.sl_app.
        reflexivity.
      - intro rx; unfold sem_pt_id; SL.normalize.
        Intro sel1. Apply sel1.
        Intro ENS.  Apply ENS.
        rewrite TF.to_of_tu, CTX.sl_app.
        unfold Sub.neg, Sub.const, ppre; cbn.
        rewrite Sub.map_app, !Vector.map_const, Sub.sub_app,
                Sub.sub_const_true, Sub.sub_const_false.
        reflexivity.
    Qed.
  End Spec.

  Global Program Instance sem_vf_repr {res_t ghout_t} : spec_sem_func (@sem_vf res_t ghout_t) := {
    sem_repr := fun vpost s => s;
  }.
  Next Obligation.
    intros pt WLP; unfold sem_vf.
    eapply FP.wlp_monotone, WLP.
    intros []; cbn; ecase TF.iso_tu as [_ ->].
    auto.
  Qed.

  Section ValueSpecRepr.
    Context [res_t : Type] [ghout_t : option (res_t -> Type)].
    Let AG := opt_sigG ghout_t.

    Section F_SPEC_VS_VAL.
      Context [vpost : Spec.vpost_t ghout_t] (s : Spec.t_vs vpost).

      Local Lemma vpost_eq
        (xG : AG)
        (sel1 : Tuple.t (Spec.sel1_t (s xG)))
        (REQ  : Spec.req s):
        VpropList.of_ctx (post (s xG sel1 REQ)) = vpost xG.
      Proof.
        apply VpropList.of_inst.
      Defined.

      Definition f_spec_vs_val :=
        let TF_A := TF.mk_p0 AG (fun x => Spec.sel1_t (s x)) in
        let TF_B := TF.mk_p  AG vpost                        in
        (FunProg.Bind
            (@FunProg.Call TF_A {|
                FunProg.Spec.pre_p  := Some (Spec.req s);
                FunProg.Spec.post_p := Some (fun REQ : Spec.req s =>
                                  TF.of_fun (fun r : TF.t TF_A =>
                  Spec.ens (s (TF.v_val r) (TF.v_sel r) REQ)));
             |})
            (fun REQ => TF.of_fun (T := TF_A) (fun r =>
             FunProg.Ret (TF.mk _ (TF.v_val r)
              (eq_rect _ VpropList.sel_t
                       (VpropList.sel_of_ctx (Spec.post (s (TF.v_val r) (TF.v_sel r) REQ)))
                       _ (vpost_eq (TF.v_val r) (TF.v_sel r) REQ)))))).

      Lemma f_spec_vs_val_correct:
        correct_Call_spec_val sem_vs s f_spec_vs_val.
      Proof.
        intros pt (REQ & WLP).
        exists REQ; cbn.
        intros xG sel1 ENS.
        fold AG in xG.
        specialize (WLP (existT _ xG (DTuple.of_tu sel1)));
          cbn in WLP; rewrite !TF.to_of_fun, TF.to_of_tu in WLP;
          specialize (WLP ENS); cbn in WLP;
          revert WLP; clear.
        unfold post, vpost_eq.
        rewrite VpropList.sel_of_inst, rew_opp_r.
        auto.
      Qed.
    End F_SPEC_VS_VAL.

    Global Instance sem_vs_repr : spec_sem_func sem_vs := {
      sem_repr := fun vpost s => f_spec_vs_val s;
      sem_repr_correct :=
        fun vpost s => f_spec_vs_val_correct s
    }.

    Variable (s : @Spec.t_r0 res_t ghout_t t_vs).

    Definition f_spec_vs sel0 :=
      Eval cbv beta delta [f_spec_vs_val] in
      f_spec_vs_val (Spec.val (s sel0)).

    Lemma f_spec_vs_correct:
      correct_Call_spec sem_vs s f_spec_vs.
    Proof.
      intro sel0; apply f_spec_vs_val_correct.
    Qed.
  End ValueSpecRepr.
  Section Impl.
    Context (f : fid) [sg : f_sig] (HSIG : SIG f = Some sg) (sgh : f_sigh sg)
            (x : f_arg_t sg).

    Definition Call_impl : @CP.instr SIG (f_retgh_t sgh).
    Proof.
      unfold f_retgh_t, opt_sigG.
      case f_ghout_t as [GO|].
      - exact (CP.Bind (CP.Call f HSIG x) (fun r =>
               CP.Bind (CP.Oracle (GO r)) (fun go =>
               CP.Ret (CP.existG _ r go)))).
      - exact (CP.Call f HSIG x).
    Defined.

    Variables (gi : OptTy.t (f_ghin_t_x sgh x)) (s : sigh_spec_t sgh x).
    Hypothesis (HSPC : fun_has_spec CT f HSIG s).

    Lemma Call_impl_correct: correct_Call_impl sem_vs (s gi) Call_impl.
    Proof.
      intros ss_id TR_id.
      pose (ss_ex := {|
        SP.Spec.pre  := SP.Spec.pre ss_id;
        SP.Spec.post := sem_pt_ex (SP.Spec.post ss_id)
      |}).
      case (HSPC ss_ex) as (ss & LE & Hss). {
        case TR_id as (sel0 & pt & SEM & SL).
        exists gi, sel0, pt. split. exact SEM.
        split. apply SL.
        intro xR; cbn; unfold sem_pt_ex, sem_pt_id in *; SL.normalize.
        eapply SLprop.ex_morph_imp; intro go.
        etransitivity. 2:apply SL.
        SL.normalize; reflexivity.
      }
      unfold fun_has_spec, spec_match in HSPC.
      unfold Call_impl, sigh_spec_t, sigh_spec_t' in *.
      destruct f_ghout_t.
      - eapply SP.Bind.
        { eapply SP.Cons, LE. apply SP.Call, Hss. }
        intro r; cbn.
        apply SP.ExistsE; intro go.
        eapply SP.Bind.
        { apply SP.Oracle with (x := go). }
        intro; apply SP.PureE; intros ->.
        apply SP.CRet; reflexivity.
      - eapply SP.Cons. { apply SP.Call, Hss. }
        rewrite LE; split; cbn. reflexivity.
        intro; unfold sem_pt_ex; Intro; reflexivity.
    Qed.

    Program Definition Call : instr (f_retgh_t sgh) := {|
      i_impl := Call_impl;
      i_spec := fun ctx => Call_Spec (s gi) (f_spec_vs (s gi)) ctx;
    |}.
    Next Obligation.
      eapply Call_spec_lem, SP.
      - intro. apply f_spec_vs_correct.
      - apply Call_impl_correct.
    Qed.
  End Impl.

  Definition Call_f_decl [sg sgh s] (fd : @f_decl sg sgh CT s)
    (x : f_arg_t sg)
    : OptTy.arrow (f_ghin_t_x sgh x)
                  (fun _ => instr (f_retgh_t sgh))
    :=
    OptTy.of_fun (fun gi =>
      Call (fd_id fd) (fd_Hsig (fd_H fd)) sgh x gi (s x) (fd_Hspec (fd_H fd) x)).
 
  Section Ghost.
    Context [sg : f_sig] [s : ghost_spec sg] (L : ghost_lem s) (x : f_arg_t sg).
    Program Definition gLem : instr (f_ret_t sg) := {|
      i_impl := CP.Oracle (f_ret_t sg);
      i_spec := fun ctx => Call_Spec (s x tt) (f_spec_vs (s x tt)) ctx;
    |}.
    Next Obligation.
      refine (Call_spec_lem Spec.sem_vs _ _  _ _ SP).
      - apply f_spec_vs_correct.
      - intros ss (sel0 & pt & (REQ & POST) & LE).
        specialize (L x sel0 REQ).
        eapply SP.Cons with (s0 := SP.Spec.mk _ _). 2:{
          rewrite <- LE; split; unfold sem_pt_id; cbn.
          - rewrite CTX.sl_app in L; exact L.
          - intro; reflexivityR.
        }
        clear LE L; SL.normalize.
        apply SP.ExistsE; intro res.
        apply SP.COracle with (x := res).
        Intro sel1; Intro ENS%POST.
        EApply; Apply ENS.
        rewrite CTX.sl_app.
        reflexivity.
    Qed.
  End Ghost.
  Section Frag.
    Context [sg : f_sig] [sgh : f_sigh sg] [p_val : p_val_t (f_ghout_t sgh)] [sem : Spec.p_val_f p_val]
            {repr : spec_sem_func sem}
            [impl : frag_impl sgh] [spec : f_spec' sgh p_val]
            (F : frag_correct sem impl spec) (x : f_arg_t sg).

    Program Definition Frag : OptTy.arrow (f_ghin_t_x sgh x) (fun _ =>
        instr (f_retgh_t sgh))
    :=
    OptTy.of_fun (fun gi => {|
      i_impl := impl x gi;
      i_spec := fun ctx => Call_Spec (spec x gi) (fun sel0 => sem_repr _ _ (Spec.val (spec x gi sel0))) ctx;
    |}).
    Next Obligation.
      eapply Call_spec_lem, SP.
      - intro; apply sem_repr_correct.
      - apply F.
    Qed.
  End Frag.

  Global Arguments f_spec_vs_val/.
  Global Arguments f_spec_vs/.
End Call.
End VProg.

Global Arguments Ret [_ _] _ {pt}.
Global Arguments RetG [_ _ _] _ _ {pt}.
Global Arguments Bind [_ _ _] _ _.
Global Arguments Call [_ _ _ _] _ _ _ [_] _.
Global Arguments Call_f_decl [_ _ _ _] _ _.
Global Arguments gLem [_ _ _] _ _.
Global Arguments Frag [_ _ _ _ sem] {repr} [impl spec] F x.

Global Arguments transform_spec [CT A ctx i s0 s1 F f].
Global Arguments Tr_change_exact [CT A ctx s csm1 prd1 F].
Global Arguments intro_impl_match1 [CT GI A GO body spec] H.
Global Arguments Impl_MatchI [CT A GO body_1 s_1 f] F [ex_sel1] EX_SEL1 WLP.
Global Arguments HasSpec_ct [CT A i ctx s f].
Global Arguments Call_SpecI [res_t ghout_t p_val s f_spec ctx sg f sel0] IJ.


Module NotationsDef.
  (* types notations *)

  Record FDecl [sg : f_sig] [sgh : f_sigh sg] (e : f_spec_exp sgh)
    : Type := mk_FDecl {
    fd_FSpec : FSpec _ e
  }.
  Global Arguments fd_FSpec [_ _ _].

  Definition fd_sig [sg sgh e] (F : @FDecl sg sgh e)
    : f_sig := sg.

  Definition fd_cp [sg sgh e] (F : @FDecl sg sgh e)
    : CP.f_spec (fd_sig F) := cp_f_spec (m_spec (fd_FSpec F)).

  Definition to_f_decl [sg sgh e] (F : @FDecl sg sgh e) (CT : CP.context)
    : Type := f_decl CT (m_spec (fd_FSpec F)).

  Definition fd_mk (f : fid) [sg sgh e] (F : @FDecl sg sgh e)
    (CT : CP.context)
    (HSIG : projT1 CT f = Some (fd_sig F))
    (HSPS : CP.fun_has_spec (projT2 CT) f HSIG = fd_cp F):
    to_f_decl F CT.
  Proof.
    exists f. unshelve eapply cp_is_declared; assumption.
  Defined.

  Definition Call_to_f_decl [sg sgh e F CT] (fd : @to_f_decl sg sgh e F CT)
    (x : f_arg_t sg) : OptTy.arrow (f_ghin_t_x sgh x) (fun _ => instr CT (f_retgh_t sgh))
    := Call_f_decl fd x.

  Coercion to_f_decl      : FDecl     >-> Funclass.
  Coercion Call_to_f_decl : to_f_decl >-> Funclass.


  Definition FragImpl [sg sgh e] (F : @FDecl sg sgh e) (CT : CP.context) : Type :=
    f_body CT sgh.

  Record FragCorrect [sg sgh e F CT] (I : @FragImpl sg sgh e F CT) := {
    get_fr_correct : frag_correct Spec.sem_vs (fun x gi => i_impl (OptTy.to_fun' (I x) gi)) (m_spec (fd_FSpec F))
  }.
  Global Arguments get_fr_correct [_ _ _ _ _ I].

  Lemma intro_FragCorrect [sg sgh e F CT I]
    (H : forall x : f_arg_t sg, impl_match CT (I x) (m_spec (fd_FSpec F) x)):
    @FragCorrect sg sgh e F CT I.
  Proof.
    constructor.
    apply impl_match_frag_correct, H.
  Qed.

  Definition Call_FragCorrect [sg sgh e F CT I] (C : @FragCorrect sg sgh e F CT I)
    (x : f_arg_t sg) : OptTy.arrow (f_ghin_t_x sgh x) (fun _ => instr CT (f_retgh_t sgh))
    := Frag (impl := fun x gi => i_impl (OptTy.to_fun' (I x) gi)) (get_fr_correct C) x.

  Coercion Call_FragCorrect : FragCorrect >-> Funclass.


  Record LDecl [arg_t : Type] [ret_t : Type] (e : f_spec_exp (lem_sigh (mk_f_sig arg_t ret_t)))
    : Type := mk_LDecl {
    ld_FSpec : FSpec _ e
  }.
  Global Arguments ld_FSpec [_ _ _].

  Definition to_ghost_lem [arg_t ret_t e] (L : @LDecl arg_t ret_t e)
    : Prop := ghost_lem (m_spec (ld_FSpec L)).

  (* NOTE it does not seem possible to declare a coercion from [to_ghost_lem] to Funclass
     with implicit [CT] (see https://github.com/coq/coq/issues/5527).
     One has to use an explicit conversion [gLem]. *)
  Coercion to_ghost_lem : LDecl >-> Sortclass.

  (* LDecl + proof, to be used with Derive *)
  Record VLem [arg_t : Type] [ret_t : Type] (e : f_spec_exp (lem_sigh (mk_f_sig arg_t ret_t)))
      (s : f_spec (lem_sigh (mk_f_sig arg_t ret_t))) : Prop := {
    vl_spec_eq :  f_spec_equiv e s;
    vl_correct :> ghost_lem s;
  }.


  Definition FImpl [CT sg sgh s] (fd : @f_decl sg sgh CT s) : Type
    := f_body CT sgh.

  Definition FCorrect [CT sg sgh s fd] (fi : @FImpl CT sg sgh s fd) : Prop
    := f_body_match fi s.
End NotationsDef.

Section F_ENTRY.
  Import NotationsDef.

  Context [sg sgh e] (F : @FDecl sg sgh e).

  Definition f_entry [A : CP.context -> Prop] (C : forall CT, A CT): CP.context_entry
    := {| CP.ce_sig := fd_sig F; CP.ce_spec := fd_cp F |}.

  Lemma has_f_entry [CT f A] C (H : CP.context_has_entry CT f (@f_entry A C)):
    to_f_decl F CT.
  Proof.
    let t := constr:(let '(exist _ H0 H1) := H in fd_mk f F CT H0 H1) in
    let t := eval cbv beta zeta delta [fd_mk cp_is_declared] in t in
    exact t.
  Defined.

  Definition f_entry_erase [CT A C] [impl : f_body CT _] [r]
    (CR : f_body_match impl (m_spec (fd_FSpec F)))
    (EX : f_erase impl)
    (E  : r = proj1_sig EX):
    CP.entry_impl_correct CT (@f_entry A C) r.
  Proof.
    rewrite E; split.
    - apply f_erase_match_spec, CR.
    - apply f_erase_oracle_free.
  Defined.
End F_ENTRY.

Module Tac.
  Export Util.Tac.

  (* If [t] is a term with a destructive let [let (...) := ?u in _] as head,
     partially instantiate [?u] by applying the constructor, allowing the let to be reduced. *)
  Ltac build_matched_shape t :=
    lazymatch t with (match ?p with _ => _ end) =>
      build_unify p ltac:(fun _ => econstructor; shelve)
    end.
  
  Ltac case_until_triv :=
    try solve [split];
    let i := fresh "i" in
    intros [|i]; [|revert i; case_until_triv].


  Ltac of_expanded_arg :=
    lazymatch goal with |- _ (match ?x with _ => _ end) ?s =>
      Tac.build_unify s ltac:(fun _ => destruct x; shelve);
      destruct x;
      nant_cbn;
      of_expanded_arg
    | _ => idtac
    end.

  (* reduces an [i_sig_t] *)
  Ltac eval_sig t k :=
    let t := eval cbn in t in
    let t := eval hnf in t in
    let t := eval cbn in t in
    k t.


  (* solves a goal [f_spec_equiv e ?s],
     instantiates [?s] *)
  Ltac build_of_expanded :=
    hnf; nant_cbn;
    intro (* arg  *); of_expanded_arg;
    intro (* gi   *); of_expanded_arg;
    refine (Spec.Expanded.of_expanded0I _ _ _); nant_cbn;
    intro (* sel0 *); of_expanded_arg;
    refine (Spec.Expanded.of_expanded1I _ _ _ _); nant_cbn;
    (* ret, TODO? allow matching *)
    try lazymatch goal with |- forall x, _ (match x with _ => _ end) _ =>
      idtac "WARNING: matching on the returned value is not supported, use projections instead"
    end;
    intro (* ret *);
    simple refine (Spec.Expanded.of_expanded2I _ _ _ _ _ _);
    [ shelve | shelve | shelve | shelve
    | (* sel1_TU_GOAL *) nant_cbn; intro (* sel1 *); Tuple.build_type_iso_tu
    | (* VPOST        *) Tac.cbn_refl
    | shelve | (* VS1 *) nant_cbn; repeat intro; refine (Spec.Expanded.of_expanded3I _) ].

  Local Lemma mk_red_FSpec [sg : f_sig] [sgh : f_sigh sg] [e : f_spec_exp sgh]
    [s0 s1 : f_spec sgh]
    (E : f_spec_equiv e s0)
    (R : s1 = s0):
    FSpec sgh e.
  Proof.
    exists s1.
    rewrite R; exact E.
  Defined.

  (* solves a goal [FSpec sig espec] *)
  Ltac build_FSpec :=
    refine (mk_red_FSpec _ _);
    [ build_of_expanded
    | cbn_refl ].

  (* solves a goal [FDecl espec] *)
  Ltac build_FDecl :=
    constructor; build_FSpec.

  (* solves a goal [LDecl espec] *)
  Ltac build_LDecl :=
    constructor; build_FSpec.

  Local Lemma mk_red_VLem [arg_t ret_t e s0 s1]
    (E : f_spec_equiv e s0)
    (R : s1 = s0)
    (L : ghost_lem s1):
    @NotationsDef.VLem arg_t ret_t e s1.
  Proof.
    split.
    - rewrite R; exact E.
    - exact L.
  Qed.

  (* on a goal [VLem e ?s],
     instantiates [?s] by solving the [vl_spec_eq] condition,
     leaves the [vl_correct] condition *)
  Ltac build_VLem :=
    lazymatch goal with |- @NotationsDef.VLem ?arg_t ?ret_t ?e ?s =>
    let s' := eval hnf in s in
    change (@NotationsDef.VLem arg_t ret_t e s');
    simple refine (mk_red_VLem _ _ _);
    [ shelve
    | (* E *) build_of_expanded
    | (* R *) nant_cbn; reflexivity
    | (* L *) try clear s ]
    end.

  (* post_hint *)

  (* pt_hint_t := (post_hint -> ltac) -> (unit -> ltac) -> ltac *)

  Ltac post_hint_Some post_hint (* : pt_hint_t *) g _ :=
    g post_hint.

  Ltac post_hint_None (* : pt_hint_t *) _ g :=
    g tt.

  Ltac get_post_hint t(* pt_hint_t *) k(* post_hint -> ltac *) :=
    t k ltac:(fun _ => fail).

  Inductive post_hint [A : Type] (post : A -> VpropList.t) : Prop := mk_post_hint.

  Ltac save_post_hint t(* pt_hint_t *) :=
    t ltac:(fun pt =>
        assert (post_hint pt) by split
      )
      ltac:(fun _ => idtac).

  Ltac load_post_hint k(* pt_hint_t -> ltac *) :=
    lazymatch goal with
    | H : post_hint ?pt |- _ =>
        clear H;
        k ltac:(fun g _ => g pt)
    | _ =>
        k ltac:(fun _ g => g tt)
    end.

  (* build_HasSpec *)

  Ltac i_sig_reflexivity :=
    nant_cbn;
    lazymatch goal with |- @i_sig_eq ?ctxn ?A ?FT ?csm0 ?prd0 ?F0 _ _ _ =>
      exact (@i_sig_eq_refl ctxn A FT csm0 prd0 F0)
    end.

  Lemma change_HasSpec_sig CT A i ctx s0 f0 csm1 prd1 F
    (H : HasSpec CT i ctx s0 f0)
    (E : i_sig_eq (FT := fun prd1 => i_spec_t s0 -> FP.instr (TF.mk_p A prd1))
           (sf_csm s0) (sf_prd s0) (fun f => f) csm1 prd1 F):
    @HasSpec CT A i ctx (mk_i_sig csm1 prd1) (F f0).
  Proof.
    destruct E, s0; exact H.
  Qed.

  (* solves a goal [TrSpec SPEC s (mk_i_sig csm prd) ?F] *)
  Ltac build_Tr_change_exact :=
    simple refine (Tr_change_exact _ _ _);
    [ (* rsel *) nant_cbn; intros; Tuple.build_shape
    | (* RSEL *) nant_cbn; intros; CTX.Trf.Tac.build_t
    | (* E    *) Tac.i_sig_reflexivity ].

  (* solves a goal [InjPre_Spec m ctx ?add s ?s' ?F]
     Leaves a goal solvable with [solve_InjPre_sig_eq] once [s] has been instanced *)
  Ltac build_InjPre :=
    lazymatch goal with |- @InjPre_Spec ?m ?ctx ?add ?A ?s ?s' ?F =>
    Tac.mk_evar (Sub.t ctx) ltac:(fun csm' =>
    Tac.mk_evar (A -> VpropList.t) ltac:(fun prd' =>
    unify s' (@mk_i_sig A ctx csm' prd');
    let ij := fresh "ij" in
    eassert (CTX.Trf.inj_p ctx m add _) as ij;
    [ CTX.Trf.Tac.build_inj_p
    | simple refine (@InjPre_SpecI m ctx add _ s _ ij csm' prd' F _); clear ]
    ))end.

  Ltac solve_InjPre_sig_eq :=
    lazymatch goal with |- ?g0 =>
    let g := eval cbn beta iota zeta delta -[CTX.Trf.Tac.build_inj_rev_f] in g0 in
    lazymatch g with (let (ncsm, rem) := CTX.Trf.Tac.build_inj_rev_f ?w0 ?w1 _ _ _ in _) =>
    let w0 := head_of w0 in
    let w1 := head_of w1 in
    cont ltac:(fun k => (let g := eval unfold w0 in g in k g) || k g) ltac:(fun g =>
    cont ltac:(fun k => (let g := eval unfold w1 in g in k g) || k g) ltac:(fun g =>
    let g := eval red_vprop_trf_wit in g in
    let g := eval cbv beta iota zeta delta [CTX.Trf.Tac.build_inj_rev_f] in g in
    lazymatch g with i_sig_eq _ _ _ _ _ _ => idtac (* OK *)
    | _ => ffail "failed to reduce InjPre_sig_eq" g0 g
    end;
    change_no_check g;
    i_sig_reflexivity
    )) end end.

  (* solves a goal [InjPre_Frame_Spec m ctx s ?s' ?F].
     Leaves a goal solvable with [solve_InjPre_sig_eq] once [s] has been instanced. *)
  Ltac build_InjPre_Frame :=
    refine (InjPre_Frame_SpecI _ _ _ _ _ _ _);
    build_InjPre.

  (* solves a goal [InjPre_SFrame_Spec m ctx s f ?s' ?f'] *)
  Ltac build_InjPre_SFrame :=
    nant_cbn;
    lazymatch goal with |- @InjPre_SFrame_Spec ?m ?ctx ?A ?s ?f ?s' ?f' =>
    Tac.mk_evar (Sub.t ctx) ltac:(fun csm' =>
    Tac.mk_evar (A -> VpropList.t) ltac:(fun prd' =>
    unify s' (@mk_i_sig A ctx csm' prd');
    simple refine (@InjPre_SFrame_SpecI m ctx A s f _ _ _ csm' prd' f' _);
    [ (* frame *) shelve | (* rev_f *) shelve
    | (* ij *) CTX.Trf.Tac.build_inj_p
    | (* E  *) solve_InjPre_sig_eq ]
    ))end.


  (* Tactics to build the instruction specifications. *)
  Global Create HintDb HasSpecDB discriminated.
  Global Hint Constants Opaque : HasSpecDB.
  Global Hint Variables Opaque : HasSpecDB.


  Ltac build_Ret pt_hint0(* pt_hint_t *) :=
    lazymatch goal with |- Ret_Spec ?x ?pt_hint1 _ _ _ =>
    simple refine (Ret_SpecI _ _ _ _ _ _  _ _);
    [ (* pt *)
      let pt_hint1_x := eval hnf in (pt_hint1 x) in
      lazymatch pt_hint1_x with
      | no_pt_hint =>
          try Tac.get_post_hint pt_hint0 ltac:(fun pt =>
            (* This can fail if the return type is not the one of the post hint,
               which can happen inside a match. *)
            exact pt);
          exact (fun _ => nil)
      | _ =>
          exact pt_hint1
      end
    | (* sels *) Tuple.build_shape
    | (* IJ   *) build_InjPre_SFrame ]
    end.

  Ltac build_Bind1_init :=
    simple refine (Bind_SpecI1 _ _ _ _ _  _ _);
    [ (* s_g *) shelve | (* f_g *) shelve | (* S_G *)
    | (* F   *) shelve | (* E *) | (* b_csm *) shelve | (* b_prd *) shelve ].

  Ltac build_Bind1 build_f :=
    build_Bind1_init;
    [ (* S_G *) build_f tt
    | (* E   *) Tac.i_sig_reflexivity ].

  Ltac build_Bind_init :=
    simple refine (Bind_SpecI _ _ _ _ _  _ _);
    [ (* s_f *) shelve | (* f_f *) shelve
    | (* S_F *) | (* f_g *) | (* S_1 *) ].

  Ltac build_Bind build_f pt_hint :=
    build_Bind_init;
    [ (* S_F *) build_f Tac.post_hint_None
    | (* f_g *) nant_cbn; intros; shelve
    | (* S_1 *) nant_cbn; intros; build_Bind1 ltac:(fun _ => build_f pt_hint) ].

  Ltac build_Call :=
    simple refine (Call_SpecI _);
    [ shelve
    | (* IJ *)
      nant_cbn;
      repeat lazymatch goal with |- InjPre_SFrame_Spec (Spec.pre ?x ++ _) _  _ _ _ _ =>
        Tac.build_matched_shape x; nant_cbn
      end;
      build_InjPre_SFrame ].


  (* match *)

  Ltac case_in_A_instr x case_x CT A i k(* A' -> i' -> rev_args -> ltac *) :=
    (* A *)
    let A_d := fresh "A'" in pose (A_d := A);
    change x with case_x in A_d;
    let A' := eval cbv delta [A_d] in A_d in clear A_d;
    (* i *)
    generalize_match_args x case_x i ltac:(fun i' rev_args =>
    k A' i' rev_args
    ).

  Ltac case_in_ctx x case_x ctx k(* ctx' -> rev_sel -> ltac *) :=
      lazymatch ctx with
      | nil => k (@nil CTX.atom) ltac:(fun _ => idtac)
      | existT _ (@Vprop.mk ?sel_ty ?vp) ?sel :: ?ctx =>
          let sel_ty' := fresh "sel_ty" in
          let vp'     := fresh "vp"     in
          pose (sel_ty' := sel_ty);
          pose (vp'     := vp  : Vprop.p sel_ty);
          fold case_x in sel_ty', vp';
          let unfold' k :=
            unfold sel_ty', vp' in *;
            let sel_ty_b := eval cbv delta [sel_ty'] in sel_ty' in
            let vp_b     := eval cbv delta [vp']     in vp'     in
            clear sel_ty' vp';
            k sel_ty_b vp_b
          in
          tryif is_independent_of sel_ty' case_x
          then (
            unfold' ltac:(fun sel_ty_b vp_b =>
            case_in_ctx x case_x ctx ltac:(fun ctx' rev_sel =>
            k (@cons CTX.atom (existT Vprop.ty (@Vprop.mk sel_ty_b vp_b) sel) ctx')
              rev_sel
          ))) else (
            let sel' := fresh "sel" in
            pose (sel' := sel : sel_ty');
            unfold' ltac:(fun sel_ty_b vp_b =>
            case_in_ctx x case_x ctx ltac:(fun ctx' rev_sel =>
            k (@cons CTX.atom (existT Vprop.ty (@Vprop.mk sel_ty_b vp_b) sel') ctx')
              ltac:(fun _ => rev_sel tt; generalize sel'; clear sel')
          )))
      | _ => fail 0 ctx
      end.

  Ltac case_in_HasSpec x
    k(* case_x -> CT -> A -> A' -> i' -> ctx -> ctx' -> s -> f ->
        rev_args(+sel) -> ltac *) :=
    lazymatch goal with |- @HasSpec ?CT ?A ?i ?ctx ?s ?f =>
    let case_x := fresh "case_x" in
    pose (case_x := x);
    case_in_A_instr x case_x CT A i ltac:(fun A' i' rev_args =>
    case_in_ctx x case_x ctx ltac:(fun ctx' rev_sel =>
    let rev_args _ := rev_sel tt; rev_args tt in

    Tac.mk_evar (Sub.t ctx) ltac:(fun csm' =>
    Tac.mk_evar (A' -> VpropList.t) ltac:(fun prd' =>
    Tac.build_term (i_spec_t (@mk_i_sig A' ctx' csm' prd')) ltac:(fun _ =>
      rev_args tt; case case_x as []; intros; shelve) ltac:(fun f' =>
    unify s (@mk_i_sig A' ctx' csm' prd');
    unify f f';
    change (@HasSpec CT A' i' ctx' (@mk_i_sig A' ctx' csm' prd') f');

    k case_x CT A A' i' ctx ctx' s f rev_args
    )))))end.

  (* destructive let *)

  Ltac build_HasSpec_dlet build_f x :=
    Tac.case_in_HasSpec x ltac:(fun case_x CT A A' i' ctx ctx' s f rev_args =>
      rev_args tt; case case_x as []; intros; nant_cbn;
      simple refine (Tac.change_HasSpec_sig CT _ _ _  _ _  _ _ _  _ _);
      [ (* s0 *) shelve | (* f0 *) shelve | (* F *) shelve
      | (* H  *) build_f tt
      | (* E  *) Tac.i_sig_reflexivity ]
    ).

  (* branch *)

  Ltac build_HasSpec_branch build_f x :=
    Tac.case_in_HasSpec x ltac:(fun case_x CT A A' i' ctx ctx' s f rev_args =>
      let ctxn := eval cbv in (length ctx) in
      Tac.build_term (list (Vector.t bool ctxn)) ltac:(fun _ =>
        clear; shelve) ltac:(fun csms1 =>

      rev_args tt; case case_x as []; (intros; nant_cbn;
      lazymatch goal with |- @HasSpec _ ?A0 ?i0 ?ctx0 ?s1 ?f1 =>
      Tac.mk_evar (i_sig_t A0 ctx0) ltac:(fun s0 =>
      simple refine (@transform_spec CT A0 ctx0 i0 s0 s1 _ _  _ _);
      [ (* F  *) shelve
      | (* f  *) shelve
      | (* H  *) build_f tt
      | (* T  *) ];
      let b_csm := eval cbn in (@sf_csm A0 ctx0 s0 : Vector.t bool ctxn) in
      Tac.elist_add csms1 b_csm
      )end);
      [
        (* First branch
             (in the order of the inductive type, not the order in the program)
           At this point, we infer the specification of the whole match in the following way:
           - We compute the union [csm1] of the consumption of each branch.
             That is, a vprop of [ctx] is in [csm1] if an only if it is consumed in at least
             a branch.
           - The production is the production of the first branch plus the vprops of [csm1] not
             consumed by the first branch. Those added vprops are taken from the context of the
             first branch, which means that the matched value is replaced by its first case. This
             may not be what one want, instead one could maybe take them from the original context. *)
        Tac.elist_end csms1;
        let csm1 := eval cbn in (@branch_csm_or ctx csms1) in
        lazymatch goal with |- @TrSpec _ ?A0 ?ctx0 ?s0 ?s1 _ =>
        refine (@TrSpec_branch_0 CT A0 ctx0  s0 csm1 _ _ csm1  _);
        i_sig_reflexivity
        end
      | .. ];
      (* other branches *)
      Tac.build_Tr_change_exact
    )).

  Local Lemma change_HasSpec_spec CT A i ctx s f0 f1
    (H : HasSpec CT i ctx s f0)
    (E : f0 = f1):
    @HasSpec CT A i ctx s f1.
  Proof.
    case E; exact H.
  Qed.

  (* solves a goal [HasSpec i ctx ?s ?f] *)
  Ltac build_HasSpec pt_hint(* pt_hint_t *) :=
    nant_cbn;
    lazymatch goal with |- @HasSpec ?C ?A ?i ?ctx ?s ?f =>
    let i' := eval hnf in i in
    intro_evar_args s ltac:(fun s' =>
    intro_evar_args f ltac:(fun f' =>
    simple refine (change_HasSpec_spec C A i' ctx s' _ f' _ _)));
    [ (* f0 *) shelve
    | (* H  *)
    lazymatch i' with
    | mk_instr _ =>
        refine (HasSpec_ct _);
        hnf;
        lazymatch goal with
        | |- Ret_Spec    _ _ _ _ _ => build_Ret pt_hint
        | |- Bind_Spec _ _ _ _ _ _ => build_Bind build_HasSpec pt_hint
        | |- Call_Spec   _ _ _ _ _ => build_Call
        | |- ?g =>
            save_post_hint pt_hint;
            solve_db HasSpecDB
        end
    | _ =>
        let i_head := Tac.head_of i'     in
        let x := Tac.matched_term i_head in
        tryif is_single_case x
        then build_HasSpec_dlet   ltac:(fun _ => build_HasSpec pt_hint) x (* destructive let *)
        else build_HasSpec_branch ltac:(fun _ => build_HasSpec pt_hint) x (* multiple branches *)
    end
    | (* E  *)
      abstract_refl
    ]
    end.

  Ltac init_HasSpec_tac k(* pt_hint_t -> ltac *) :=
    load_post_hint k.

  (* solves a goal [HasSpec i ctx (mk_i_sig csm prd) ?f] *)
  Ltac build_HasSpec_exact :=
    lazymatch goal with |- HasSpec _ _ _ (mk_i_sig _ ?prd) _ =>
    refine (transform_spec _ _);
    [ build_HasSpec ltac:(post_hint_Some prd)
    | build_Tr_change_exact ]
    | _ => ffail "build_HasSpec_exact"
    end.


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
        nant_cbn; repeat intro; eassumption
        |]
      | (* otherwise, conitinue with the next [exists] *)
        refine (Morphisms_Prop.ex_iff_morphism _ _ (fun x => _))
      | (* if no more [exists] remains *)
        reflexivity
      ]
    | nant_cbn;
      repeat refine (Morphisms_Prop.ex_iff_morphism _ _ (fun x => _));
      refine (simpl_tuple_eq_conj _ _);
      (* remove trivial equalities [x = x] *)
      [ nant_cbn;
        repeat first [ refine (simpl_and_list_r1 eq_refl _)
                     | refine (simpl_and_list_e1 _) ];
        exact simpl_and_list_0
      | nant_cbn; reflexivity ]
    ].

  Ltac build_impl_match_init :=
    (* destruct arg *)
    nant_cbn;
    repeat lazymatch goal with
    |- impl_match _ _ (match ?x with _ => _ end) => destruct x; nant_cbn
    end;
    refine (intro_impl_match1 _); nant_cbn;
    (* intro and destruct gi *)
    intro;
    repeat lazymatch goal with
    |- forall _ : Spec.sel0_t (match ?x with _ => _ end), _ => destruct x; nant_cbn
    end;
    (* intro and destruct sel0 *)
    intro;
    repeat lazymatch goal with
    |- Impl_Match _ _ (match ?x with _ => _ end) => destruct x; nant_cbn
    end;

    simple refine (Impl_MatchI _ _ _);
    [ (* f *) shelve | (* F *) nant_cbn | (* ex_sel1 *) shelve
    | (* EX_SEL1 *) nant_cbn; repeat intro; simplify_ex_eq_tuple
    | (* WLP *) ].

  (* change a goal [impl_match CT vprog spec] into a condition [forall (REQ : req), wlp f post] *)
  Ltac build_impl_match :=
    build_impl_match_init;
    [ (* F   *) build_HasSpec_exact
    | (* WLP *) nant_cbn ].

  Lemma erase_cont_change [SG A B i k] r0 [r1]
    (C : CP.erase_cont i k r0)
    (E : r0 = r1):
    @CP.erase_cont SG A B i k r1.
  Proof.
    subst; exact C.
  Qed.

  Ltac build_erase_cont_match build_f x :=
    lazymatch goal with |- @CP.erase_cont ?SG ?A ?B (@i_impl ?CT _ ?i) ?k ?r =>
    (* A B k *)
    let i_v := fresh "i" in
    let F_d := fresh "F'" in
    pose (F_d := fun i_v : instr CT A =>
      @CP.erase_cont SG A B (@i_impl CT A i_v) k);
    let case_x := fresh "case_x" in
    set (case_x := x) in F_d;
    let F' := eval cbv delta [F_d] in F_d in clear F_d;
    (* i *)
    Tac.generalize_match_args x case_x i ltac:(fun i' rev_args =>

    change (F' i' r); cbn beta;
    simple refine (Tac.erase_cont_change _ _ _);
    [ (* r0 *) rev_args tt; case case_x as []; intros; shelve
    | (* C  *) rev_args tt; case case_x as []; intros;
      build_f tt
    | (* E  *) CP.simplify_match case_x ]
    )end.

  Ltac build_erase_cont :=
    nant_cbn;
    lazymatch goal with | |- @CP.erase_cont ?SG ?A ?B ?i ?k ?r =>
    intro_evar_args r ltac:(fun r' =>
    change (@CP.erase_cont SG A B i k r');

    lazymatch i with
    | i_impl ?v =>
        let v_head := head_of v in
        lazymatch v_head with
        | (match ?x with _ => _ end) =>
            build_erase_cont_match ltac:(fun _ => build_erase_cont) x
        | _ =>
            let v' := eval hnf in v in
            progress change (@CP.erase_cont SG A B (i_impl v') k r');
            build_erase_cont
        end
    | _ =>
        CP.build_erase_cont_k build_erase_cont
    end)
    | |- ?g => fail "build_erase_cont" g
    end.

  (* solves a goal [f_erase bd] *)
  Ltac erase_impl :=
    eexists; intro;
    refine (CP.erase_by_cont _ _ _);
    [ build_erase_cont
    | Tac.cbn_refl
    | try solve [ CP.build_oracle_free ] ].

  (* [assumption] but with only alpha conversion on some subterms *)
  Ltac f_entry_assumption :=
    lazymatch goal with |- NotationsDef.to_f_decl ?f _ =>
    lazymatch goal with H : NotationsDef.to_f_decl f _ |- _ => exact H
    | _ => ffail "failed to find f_decl assumption" f
    end
    | _ => ffail "Not a known f_entry assumption" end.

  (* solves a goal [CP.entry_impl_correct CT (f_entry F PF) ?impl] *)
  Ltac build_f_entry_impl_correct :=
    lazymatch goal with |- CP.entry_impl_correct _ (f_entry _ ?C) _ =>
    simple refine (f_entry_erase _ _ _ _);
    [ shelve
    | unshelve eapply C; f_entry_assumption
    | Tac.erase_impl
    | cbn; reflexivity ]
    end.

End Tac.

(* Exported tactics *)

Module ExtractTactics.
  #[export] Hint Extern 1 (Tac.Arrow (CP.context_has_entry _ _ (f_entry _ _)) _) =>
     exact (Tac.mk_Arrow (has_f_entry _ _)) : extractDB.
  
  #[export] Hint Extern 1 (CP.entry_impl_correct _ (f_entry _ _) _) =>
     Tac.build_f_entry_impl_correct : extractDB.
End ExtractTactics.
Export ExtractTactics.

Module Tactics.
  #[export] Hint Extern 1 (NotationsDef.FDecl _) => Tac.build_FDecl : DeriveDB.
  #[export] Hint Extern 1 (NotationsDef.LDecl _) => Tac.build_LDecl : DeriveDB.

  #[export] Hint Extern 1 (f_erase _) => Tac.erase_impl : DeriveDB.

  (* Changes a goal [f_body_match impl spec] into a goal [pre -> FP.wlpa f post]
     where [f : FP.instr _] is a functionnal program.
     It can also be applied to goals [FCorrect] and [FragCorrect]. *)
  Ltac build_fun_spec :=
    lazymatch goal with
    | |- NotationsDef.FragCorrect _ => refine (NotationsDef.intro_FragCorrect _)
    | _ => idtac
    end;
    intro (* arg *);
    Tac.build_impl_match;
    do 2 FunProg.simpl_prog.

  (* Changes a goal [f_body_match impl spec] into a WLP *)
  Ltac by_wlp :=
    build_fun_spec;
    FunProg.by_wlp.

  Ltac solve_by_wlp :=
    build_fun_spec;
    FunProg.solve_by_wlp.

  (* start the proof of a ghost lemma *)
  Ltac init_lemma0 :=
    lazymatch goal with
    | |- NotationsDef.VLem _ _ => Tac.build_VLem
    | |- _ => idtac
    end;
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
  Global Arguments FDecl [_ _] e%vprog_spec.
  Global Arguments LDecl [_ _] e%vprog_spec.
  Global Arguments VLem  [_ _] e%vprog_spec.


  Definition mk_f_r0_None (arg_t : Type) [res_t ghout_t]
    (f : arg_t -> @Spec.Expanded.t_r0 res_t ghout_t):
    f_spec_exp (mk_f_sigh (mk_f_sig arg_t res_t) None ghout_t)
    := fun arg _ => f arg.
  Definition mk_f_r0_Some (arg_t : Type) (ghin_t : arg_t -> Type) [res_t ghout_t]
    (f : forall (x : arg_t) (y : ghin_t x), @Spec.Expanded.t_r0 res_t ghout_t):
    f_spec_exp (mk_f_sigh (mk_f_sig arg_t res_t) (Some ghin_t) ghout_t)
    := fun arg => f arg.

  Definition mk_f_r2_None (A : Type) [req : Prop] (f : A -> Spec.Expanded.t_r2 req)
    (x : @Spec.opt_sigG A None) : Spec.Expanded.t_r2 req :=
    f x.
  Definition mk_f_r2_Some (A : Type) [req : Prop] (GO : A -> Type)
    (f : forall (x : A) (y : GO x), Spec.Expanded.t_r2 req)
    (x : @Spec.opt_sigG A (Some GO)) : Spec.Expanded.t_r2 req :=
    CP.split_sigG f x.

  Global Arguments mk_f_r0_None/.
  Global Arguments mk_f_r0_Some/.
  Global Arguments mk_f_r2_None/.
  Global Arguments mk_f_r2_Some/.

  Notation "'SPEC' ( arg : arg_ty ) s" :=
    (mk_f_r0_None (arg_ty <: Type)%type (fun arg => s))
    (at level 0,
     arg pattern at level 95, arg_ty constr at level 200,
     s custom vprog_spec_0 at level 0) : vprog_spec_scope.
  Notation "'SPEC' ( arg : arg_ty ) & ( gi : gi_ty ) s" :=
    (mk_f_r0_Some (arg_ty <: Type)%type (fun arg => (gi_ty <: Type)%type) (fun arg gi => s))
    (at level 0,
     arg pattern at level 95, arg_ty constr at level 200,
     gi  pattern at level 95, gi_ty  constr at level 200,
     s custom vprog_spec_0 at level 0) : vprog_spec_scope.

  Notation "' sel0 prs pre req s" :=
    (Spec.Expanded.mk_r0 (fun sel0 =>
     Spec.Expanded.mk_r1 prs pre req s))
    (in custom vprog_spec_0 at level 0,
     sel0 pattern at level 0, prs constr at level 0, pre constr at level 0, req constr at level 0,
     s custom vprog_spec_1 at level 0).

  Notation "& REQ ' ( res : res_ty ) & ( go : go_ty ) sel1 s" :=
    (mk_f_r2_Some (res_ty <: Type)%type (fun res => (go_ty <: Type)%type) (fun res go =>
     Spec.Expanded.mk_r2 (fun sel1 REQ => s)))
    (in custom vprog_spec_1 at level 0,
     REQ name,
     res name, res_ty constr at level 200,
     go name,  go_ty  constr at level 200,
     sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).
  Notation "& REQ ' ( res : res_ty ) sel1 s" :=
    (mk_f_r2_None (res_ty <: Type)%type (fun res =>
     Spec.Expanded.mk_r2 (fun sel1 REQ => s)))
    (in custom vprog_spec_1 at level 0,
     REQ name,
     res name, res_ty constr at level 200,
     sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).
  Notation "' ( res : res_ty ) & ( go : go_ty ) sel1 s" :=
    (mk_f_r2_Some (res_ty <: Type)%type (fun res => (go_ty <: Type)%type) (fun res go =>
     Spec.Expanded.mk_r2 (fun sel1 _ => s)))
    (in custom vprog_spec_1 at level 0,
     res name, res_ty constr at level 200,
     go name,  go_ty  constr at level 200,
     sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).
  Notation "' ( res : res_ty ) sel1 s" :=
    (mk_f_r2_None (res_ty <: Type)%type (fun res =>
     Spec.Expanded.mk_r2 (fun sel1 _ => s)))
    (in custom vprog_spec_1 at level 0,
     res name, res_ty constr at level 200,
     sel1 pattern at level 0,
     s custom vprog_spec_2 at level 0).

  Notation "post ens" := (Spec.Expanded.mk_r3 post ens)
    (in custom vprog_spec_2 at level 0,
     post constr at level 0, ens constr at level 0).
End Notations.
