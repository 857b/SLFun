From SLFun Require Import Util Values SL VProg.Vprop VProg.Core.
From Coq   Require Import Lists.List.

Import ListNotations SLNotations VProg.Core.Abbrev.
Import SL.Tactics.


Section Read.
  Context [CT : CP.context] (p : ptr).

  Inductive Read_Spec (ctx : CTX.t) (s : i_sig_t memdata ctx) (f : i_spec_t s) : Prop
    := Read_SpecI
    (d : memdata)
    (IJ : InjPre_SFrame_Spec [CTX.mka (SLprop.cell p, d)] ctx {|
      sf_csm  := Vector.cons _ false _ (Vector.nil _) <: Sub.t [_];
      sf_prd  := fun _ => nil;
    |} (FunProg.Ret (TF.mk0 _ d Tuple.tt)) s f).

  Program Definition Read : instr CT memdata := {|
    i_impl := CP.Read p;
    i_spec := fun ctx => Read_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_SFrame IJ); clear IJ.
    do 2 intro; cbn in *.
    eapply SP.Cons.
      { apply SP.Read with (d := d). }
    split; cbn.
    - SL.normalize; reflexivity.
    - intro; SL.normalize.
      Intro ->.
      Apply PRE.
      reflexivity.
  Qed.
End Read.

Local Ltac build_Read :=
  simple refine (Read_SpecI _ _ _ _ _ _);
  [ shelve | (* IJ *) Tac.build_InjPre_SFrame ].

Section Write.
  Context [CT : CP.context] (p : ptr) (d : memdata).

  Inductive Write_Spec (ctx : CTX.t) (s : i_sig_t unit ctx) (f : i_spec_t s): Prop
    := Write_SpecI
    (d0 : memdata)
    (IJ : InjPre_SFrame_Spec [CTX.mka (SLprop.cell p, d0)] ctx {|
      sf_csm  := Vector.cons _ true _ (Vector.nil _) <: Sub.t [_];
      sf_prd  := fun _ => [Vprop.mk (SLprop.cell p)];
    |} (FunProg.Ret (TF.mk0 (fun _ => [memdata]) tt (d, tt))) s f).

  Program Definition Write : instr CT unit := {|
    i_impl := CP.Write p d;
    i_spec := fun ctx => Write_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_SFrame IJ); clear IJ.
    do 2 intro; cbn in *.
    eapply SP.Cons.
      { apply SP.Write with (d0 := d0). }
    split; cbn.
    - SL.normalize; reflexivity.
    - intros [].
      Apply (d, tt).
      Apply PRE.
      SL.normalize; reflexivity.
  Qed.
End Write.

Local Ltac build_Write :=
  simple refine (Write_SpecI _ _ _ _ _ _ _);
  [ shelve | (* IJ *) Tac.build_InjPre_SFrame ].

Section Loop.
  Context [CT : CP.context] [A B : Type]
    (* ALT? like function spec / Assert *)
    (vinv : A + B -> VpropList.t)
    (sinv : option (forall x : A + B, Tuple.arrow (VpropList.sel (vinv x)) (fun _ => Prop)))
    (ini : A + B) (f : A -> instr CT (A + B)).

  Fixpoint split_sub_of_ctx1 (vs : VpropList.t) (add : CTX.t) {struct vs}:
    forall (sl : VpropList.sel_t (vs ++ VpropList.of_ctx add))
           (sb : Sub.t (VpropList.inst (vs ++ VpropList.of_ctx add) sl)),
    CTX.t * Sub.t add.
  Proof.
    case vs as [|v vs]; cbn.
    - exact (fun sl sb => ([], VpropList.tr_sub_of_ctx sb)).
    - intros (s, sl) [b sb]%Sub.uncons.
      exact (
        let (r_vs, r_sb) := split_sub_of_ctx1 vs add sl sb in
        (if b then r_vs else existT _ v s :: r_vs, r_sb)
      ).
  Defined.

  Lemma split_sub_of_ctx1_sl vs add ncsm csm1 sl1i sl1a csm:
    let sl1a' := VpropList.change_ctx_sub add csm1 sl1a in forall
    (E : split_sub_of_ctx1 vs add (VpropList.app_sel sl1i sl1a') csm = (ncsm, csm1)),
    SLprop.eq
      (CTX.sl (CTX.sub (VpropList.inst (vs ++ VpropList.of_ctx add) (VpropList.app_sel sl1i sl1a'))
                       (Sub.neg csm)))
      (CTX.sl ncsm ** CTX.sl (CTX.sub add (Sub.neg csm1))).
  Proof.
    revert sl1i csm ncsm; induction vs as [|v vs]; cbn.
    - intros _ ? ?.
      injection 1 as <- E; SL.normalize.
      induction add as [|[] add].
      + reflexivity.
      + destruct csm1 as [[|] csm1] using Sub.caseS';
        cbn in sl1a.
        * destruct sl1a as (sl0, sl1a); cbn in csm.
          destruct csm as [b csm] using Sub.caseS'.
          cbn in E; apply Vector.cons_inj in E as [-> E].
          apply IHadd in E.
          cbn; exact E.
        * cbn in csm.
          destruct csm as [b csm] using Sub.caseS'.
          cbn in E; apply Vector.cons_inj in E as [-> E].
          apply IHadd in E.
          cbn; rewrite E; reflexivity.
    - intros (sl, sl1i) csm ?.
      case csm as [b csm] using Sub.caseS'; cbn.
      specialize (IHvs sl1i csm); cbn in IHvs.
      destruct split_sub_of_ctx1 as (r_vs, r_sb).
      specialize (IHvs r_vs).
      injection 1 as <- <-.
      case b; cbn; rewrite IHvs by reflexivity;
      SL.normalize; reflexivity.
  Qed.

  Let m (sel0 : VpropList.sel_t (vinv ini)) : CTX.t := VpropList.inst (vinv ini) sel0.

  Section Loop_Spec1.
    Variables (sel0 : VpropList.sel_t (vinv ini))
              (add  : CTX.t)
              (csm1 : Sub.t add).

    Let vs1 (x : A + B) := vinv x ++ VpropList.of_ctx add.
    Let vs2 (x : A + B) := vinv x ++ VpropList.of_ctx (CTX.sub add csm1).
    Let RA  := TF.mk_p A (fun x => (vs1 (inl x))).
    Let ctx1 (r : TF.t RA) := VpropList.inst (vs1 (inl (TF.v_val r))) (TF.v_sel r).

    Definition r1_of_sub
      (v : A)
      (sl : TF.t (TF.p_tu (VpropList.sel (vinv (inl v) ++ VpropList.of_ctx (CTX.sub add csm1))))):
      TF.t (TF.mk_p A (fun x => vinv (inl x) ++ VpropList.of_ctx add)).
    Proof.
      exists v.
      apply TF.of_tu.
      apply TF.to_tu, VpropList.split_sel in sl as (sl0, sl1).
      exact (VpropList.app_sel sl0 (VpropList.change_ctx_sub add csm1 sl1)).
    Defined.

    Let s_f_t :=
      TF.arrow RA (fun r1 => i_sig_t (A + B) (ctx1 r1)).
    Let f_f_t (s_f : s_f_t) :=
      TF.arrow RA (fun r1 => i_spec_t (TF.to_fun s_f r1)).
    Let sel2_t (s_f : s_f_t) :=
      TF.arrow RA (fun r1 => TF.arrow (sf_rvar (TF.to_fun s_f r1)) (fun r2 =>
        VpropList.sel_t (vs2 (TF.v_val r2)))).

    Let sel_0 :=
      VpropList.app_sel sel0 (VpropList.sel_of_ctx (CTX.sub add csm1)).
    Let ret_2 (f_s : s_f_t) (sel2 : sel2_t f_s) (r1 : TF.t RA) (r2 : sf_rvar_t (TF.to_fun f_s r1)):
      TF.mk_t (A + B) vs2 :=
      TF.mk _ (TF.v_val r2) (TF.to_fun (TF.to_fun sel2 r1) r2).
      

    Definition loop_sf_spec1 (s_f : s_f_t) (f_f : f_f_t s_f) (sel2 : sel2_t s_f)
        (Inv : TF.arrow (TF.mk_p (A+B) vs2) (fun _ => Prop)):
      FP.instr (TF.mk_p B (fun x : B => vs2 (inr x))) :=
      @FunProg.Loop A B (fun x => TF.p_tu (VpropList.sel (vs2 x)))
        Inv
        ini (TF.of_tu sel_0)
        (fun x : A => DTuple.of_fun (fun r1a =>
         let r1 : TF.t RA := r1_of_sub x r1a in
         FunProg.Bind (TF.to_fun f_f r1) (TF.of_fun (fun r2 =>
         FunProg.Ret (ret_2 s_f sel2 r1 r2))))).

    Local Transparent FP.Bind FP.Ret FP.Loop.
    Local Opaque ret_2 r1_of_sub TF.to_fun.

    Lemma loop_sf_spec1_wlp f_s f_f sel2 Inv post
      (WLP : FP.wlp (loop_sf_spec1 f_s f_f sel2 Inv) post):
      TF.to_fun Inv (TF.mk _ ini sel_0) /\
      (forall x1 sl1,
        let r1 : TF.t RA := r1_of_sub x1 (TF.of_tu sl1) in
        TF.to_fun Inv (TF.mk _ (inl x1) sl1) ->
        FP.wlp (TF.to_fun f_f r1) (fun r2 => TF.to_fun Inv (ret_2 f_s sel2 r1 r2))) /\
      (forall x3 sl3,
        TF.to_fun Inv (TF.mk _ (inr x3) sl3) ->
        post (TF.mk _ x3 sl3)).
    Proof.
      cbn in WLP; case WLP as (INI & PRS & EXIT).
      split; [|split].
      - exact INI.
      - intros x1 sl1 r1 INV1.
        specialize (PRS x1 (TF.of_tu sl1) INV1).
        rewrite TF.to_of_fun in PRS.
        cbn in PRS; fold r1 in PRS.
        eapply FP.wlp_monotone, PRS; cbn; intro r2.
        rewrite DTuple.to_of_fun; cbn; auto.
      - intros x3 sl3.
        exact (EXIT x3 (TF.of_tu sl3)).
    Qed.

    Local Opaque loop_sf_spec1.
    Local Transparent r1_of_sub.

    Variable (EX :
      forall (R : DTuple.p)
             (f : forall Inv : TF.arrow (TF.mk_p (A + B) vs2) (fun _ => Prop),
                  FP.instr R),
      FP.instr R).

    Inductive Loop_Spec1 : forall s : i_sig_t B (m sel0 ++ add), i_spec_t s -> Prop
      := Loop_Spec1I
      (s_f : s_f_t) (f_f : f_f_t s_f)
      (S_F : TF.arrow RA (fun r =>
        HasSpec CT (f (TF.v_val r)) (ctx1 r) (TF.to_fun s_f r) (TF.to_fun f_f r)))
      (sel2_f : sel2_t s_f)
      (E : TF.arrow RA (fun r1 =>
        let (ncsm, csm_add) :=
          split_sub_of_ctx1 (vinv (inl (TF.v_val r1))) add
                            (TF.v_sel r1) (sf_csm (TF.to_fun s_f r1)) in
        csm1 = csm_add /\
        TF.all (sf_rvar (TF.to_fun s_f r1)) (fun r2 => inhabited (
          CTX.Trf.t (sf_prd_ctx (TF.to_fun s_f r1) r2 ++ ncsm)
                    (VpropList.inst (vs2 (TF.v_val r2)) (TF.to_fun (TF.to_fun sel2_f r1) r2))))))
      [l_F] (EF : l_F = fun f_f : f_f_t s_f => EX _ (loop_sf_spec1 s_f f_f sel2_f)):
      Loop_Spec1 {|
        sf_csm  := Sub.app (Sub.const (m sel0) true) csm1;
        sf_prd  := fun x : B => vs2 (inr x);
      |} (l_F f_f).

    Lemma Loop_Spec1_correct
      (EX_correct : forall R f post, FP.wlp (EX R f) post -> exists Inv, FP.wlp (f Inv) post)
      s_l f_l (SP : Loop_Spec1 s_l f_l):
      sound_spec CT (CP.Loop ini (fun x0 : A => i_impl (f x0))) (m sel0 ++ add) s_l f_l.
    Proof.
      destruct SP; do 2 intro; subst l_F; cbn in post, PRE.
      apply EX_correct in PRE as (Inv & (INI & PRS & EXIT)%loop_sf_spec1_wlp).
      clear EX_correct.
      pose (sl_inv := fun x : A + B =>
        SLprop.ex (VpropList.sel_t (vs2 x)) (fun sl =>
        SLprop.pure (TF.to_fun Inv (TF.mk _ x sl)) **
        CTX.sl (VpropList.inst (vs2 x) sl) **
        CTX.sl (CTX.sub add (Sub.neg csm1)))%slprop).

      eapply SP.Cons. {
        apply SP.Loop with (inv := sl_inv).
        intro x1; unfold sl_inv.
        apply SP.ExistsE; intro sl1.
        apply SP.PureE;   intro INV1.
        pose (r1  := r1_of_sub x1 (TF.of_tu sl1)).
        apply TF.to_fun with (x := r1) in S_F, E.
        eapply SP.Cons.
          { apply S_F, PRS, INV1. }
        clear S_F PRS INV1.

        subst s_f_t f_f_t sel2_t ret_2 ctx1; cbn beta in *.
        set (r1'     := r1_of_sub _ _); change r1' with r1; clear r1'.
        set (sel2_f1 := TF.to_fun sel2_f r1) in *; clearbody sel2_f1; clear sel2_f; cbn in sel2_f1.
        set (f_f1    := TF.to_fun f_f r1) in *; clearbody f_f1; clear f_f; cbn in f_f1.
        set (s_f1    := TF.to_fun s_f r1) in *.
          set (t := TF.to_fun _ _) in sel2_f1; change t with s_f1 in sel2_f1; clear t;
          set (t := TF.to_fun _ _) in f_f1;    change t with s_f1 in f_f1;    clear t;
          clearbody s_f1; clear s_f; cbn in s_f1.
        unfold r1_of_sub in r1.
        set (t := VpropList.split_sel _ _ _) in r1, s_f1, f_f1, sel2_f1; subst r1.
        set (t' := TF.to_tu _) in t;
          assert (t' = sl1) by apply TF.to_of_tu;
          clearbody t'; subst t'.
        cbn in E.
        specialize (VpropList.app_split_sel _ _ sl1) as sl1_eq;
          fold t in sl1_eq; case t as [sl1i sl1a]; cbn in sl1_eq;
          subst sl1.
        cbn in E; cbn.
        set (t := TF.to_tu _) in s_f1, f_f1, E, sel2_f1; fold t.
        eassert (t = _) by apply TF.to_of_tu; clearbody t; subst t.

        split; unfold sf_post, sf_post_ctx; cbn.
        - unfold vs1, vs2; cbn.
          rewrite !VpropList.inst_app, !CTX.sl_app, VpropList.change_ctx_sub_sl.
          SL.normalize; setoid_rewrite SLprop.star_comm at 2; reflexivity.
        - intro x2; SL.normalize.
          Intro sel2.
          Intro POST.
          pose (r2 := TF.mk (sf_prd s_f1) x2 sel2);
            change (existT _ x2 (TF.of_tu sel2)) with r2.
          Apply (TF.to_fun sel2_f1 r2).
          Apply POST; clear POST.
          subst vs1; cbn.
          case split_sub_of_ctx1 as (ncsm, csm_add) eqn:E_eq in E;
            case E as [<- E];
            rewrite TF.all_iff in E; specialize (E r2);
            case E as [E%CTX.Trf.t_fwd].
          etransitivity.
            2:apply SLprop.star_morph_imp; [exact E | reflexivity].
          rewrite !CTX.sl_app; SL.normalize.
          apply split_sub_of_ctx1_sl in E_eq as ->.
          reflexivity.
      }
      clear E PRS.
      split; unfold sf_post, sl_inv; cbn.
      - unfold vs2, m.
        Apply sel_0.
        Apply INI.
        unfold sel_0.
        rewrite VpropList.inst_app, VpropList.inst_of_ctx, !CTX.sl_app,
                (CTX.sl_split add csm1).
        SL.normalize; reflexivity.
      - intro x3.
        unfold vs2, m, sl_inv.
        Intro sel3. Intro INV3.
        Apply sel3.
        Apply. apply EXIT, INV3.
        clear.
        unfold Sub.neg, Sub.const.
        rewrite TF.to_of_tu, CTX.sl_app, Sub.map_app, Vector.map_const,
                Sub.sub_app, Sub.sub_const_false.
        reflexivity.
    Qed.
  End Loop_Spec1.

  Inductive Loop_Spec (ctx : CTX.t): forall s : i_sig_t B ctx, i_spec_t s -> Prop
    := Loop_SpecI
    (sel0 : VpropList.sel_t (vinv ini))
    (add  : CTX.t)
    (csm1 : Sub.t add)
    (s_l  : i_sig_t B (m sel0 ++ add)) (f_l : i_spec_t s_l)
    [s' F]
    (IJ   : InjPre_Spec (m sel0) ctx add s_l s' F)
    (L1   : Loop_Spec1 sel0 add csm1 (fun R f =>
              let ivp  (x : A + B) := vinv x ++ VpropList.of_ctx (CTX.sub add csm1) in
              match sinv with
              | Some sinv =>
                  f (fun (x : A + B) => TF.of_fun (T := TF.p_tu (VpropList.sel (ivp x))) (fun sel =>
                     let (seli, _) := VpropList.split_sel (vinv x) (VpropList.of_ctx (CTX.sub add csm1))
                                        (DTuple.to_tu sel) in
                     Tuple.to_fun (sinv x) seli))
              | None =>
                  FunProg.Bind
                  (FunProg.Oracle (DTuple.Psingl
                    (forall x : A + B, DTuple.arrow (DTuple.p_tu (VpropList.sel' (ivp x))) (fun _ => Prop))))
                  f
              end) s_l f_l):
    Loop_Spec ctx s' (F f_l).
  
  Program Definition Loop0 : instr CT B := {|
    i_impl := CP.Loop ini (fun x => i_impl (f x));
    i_spec := fun ctx => Loop_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre  IJ); clear IJ.
    eapply Loop_Spec1_correct, L1; clear;
    intros R f post; case sinv as [|].
    - intro H; eexists; exact H.
    - intros [[Inv []] H]. exists Inv; exact H.
  Qed.

  Global Arguments loop_sf_spec1/.
End Loop.
Definition Loop [CT A B]
  {inv : opt_arg (A + B -> list Vprop.t) (fun _ => [])}
  (ini : A + B)
  (body : A -> instr CT (A + B)):
  instr CT B
  := Loop0 inv None ini body.

Definition Loop_inv [CT A B]
  (inv : A + B -> {v : list Vprop.t & Tuple.arrow (VpropList.sel v) (fun _ => Prop)})
  (ini : A + B)
  (body : A -> instr CT (A + B)):
  instr CT B
  := Loop0 (fun x => projT1 (inv x)) (Some (fun x => projT2 (inv x))) ini body.

Ltac build_Loop :=
  lazymatch goal with |- Loop_Spec ?vinv _ _ _ _ _ _ =>
  simple refine (Loop_SpecI _ _ _ _ _ _ _ _ _ _ _ _);
  [ (* sel0 *) cbn; Tuple.build_shape
  | (* add  *) shelve | (* csm1 *) shelve
  | (* s_l  *) shelve | (* f_l  *) shelve | (* F *) shelve
  | (* IJ   *) Tac.build_InjPre
  | (* L1   *)
    simple refine (Loop_Spec1I _ _ _ _ _ _ _ _ _ _ _ _ _);
    [ (* s_f    *) shelve | (* f_f *) shelve
    | (* S_F    *) cbn; intros; Tac.build_HasSpec ltac:(Tac.post_hint_Some vinv)
    | (* sel2_f *) (* wait for csm1 *)
    | (* E      *) cbn; intros; split; [reflexivity (* csm1 *)|]
    | (* l_F    *) shelve | (* EF *) ];
    [ (* sel2_f *) cbn; intros; Tuple.build_shape
    | (* E      *) cbn; intros; constructor; CTX.Trf.Tac.build_t
    | (* EF     *) Tac.cbn_refl ]
  ];
  (* IJ spec eq *) Tac.solve_InjPre_sig_eq
  end.


Module Tactics.
  #[export] Hint Extern 1 (Read_Spec       _ _ _ _) =>
    Tac.init_HasSpec_tac ltac:(fun _ => build_Read)  : HasSpecDB.
  #[export] Hint Extern 1 (Write_Spec    _ _ _ _ _) =>
    Tac.init_HasSpec_tac ltac:(fun _ => build_Write) : HasSpecDB.
  #[export] Hint Extern 1 (Loop_Spec _ _ _ _ _ _ _) =>
    Tac.init_HasSpec_tac ltac:(fun _ => build_Loop)  : HasSpecDB.
End Tactics.
Export Tactics.
