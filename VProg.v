Require Import SLFun.Util SLFun.Values SLFun.SL.
Require SLFun.ConcreteProg SLFun.SLProg SLFun.FunProg.

Require Import Coq.Lists.List.

Import SLNotations.
Import ListNotations.


Module Vprop.
  Record t := mk {
    ty : Type;
    sl : ty -> SLprop.t;
  }.
  Global Arguments mk [ty].
End Vprop.

Module CTX.
  Definition atom := {v : Vprop.t & Vprop.ty v}.

  Definition mka [A : Type] (arg : (A -> SLprop.t) * A) : atom :=
    let (sl, x) := arg in
    existT Vprop.ty (Vprop.mk sl) x.

  Definition sla (a : atom): SLprop.t :=
    Vprop.sl (projT1 a) (projT2 a).

  Definition t := list atom.

  Definition sl : t -> SLprop.t :=
    List.fold_right (fun a => SLprop.star (sla a)) SLprop.emp.

  Definition app : t -> t -> t := @List.app atom.

  Lemma sl_app (c0 c1 : t):
    SLprop.eq (sl (app c0 c1)) (sl c0 ** sl c1).
  Proof.
    induction c0; simpl; SLprop.normalize; [|rewrite IHc0]; reflexivity.
  Qed.

  Module Sub.
    Definition t (c : CTX.t) := Vector.t bool (List.length c).

    Fixpoint sub (c : CTX.t) : t c -> CTX.t :=
      match c with
      | nil     => fun _ => nil
      | x :: xs => fun s =>
          let (hd, tl) := Vector.uncons s in
          let ys := sub xs tl in
          if hd then x :: ys else ys
      end.

    Definition const (c : CTX.t) (v : bool) : t c :=
      Vector.const v (List.length c).
  
    Lemma sub_const_true c:
      sub c (Sub.const c true) = c.
    Proof.
      induction c; simpl; f_equal; auto.
    Qed.
    
    Lemma sub_const_false c:
      sub c (Sub.const c false) = nil.
    Proof.
      induction c; simpl; f_equal; auto.
    Qed.

    Definition neg [c : CTX.t] : t c -> t c :=
      Vector.map negb.

    Definition or [c : CTX.t] : t c -> t c -> t c :=
      Vector.map2 orb.
    
    Definition and [c : CTX.t] : t c -> t c -> t c :=
      Vector.map2 andb.

    Definition minus [c : CTX.t] : t c -> t c -> t c :=
      Vector.map2 (fun b0 b1 => andb b0 (negb b1)).

    Fixpoint app [c0 c1 : CTX.t] : forall (s0 : t c0) (s1 : t c1), t (c0 ++ c1).
    Proof.
      case c0 as [|hd c0].
      - intros _ s1. exact s1.
      - intros s0 s1.
        case s0 as [hd0 tl0] using Vector.caseS'.
        constructor.
        + exact hd0.
        + exact (app c0 c1 tl0 s1).
    Defined.

    Lemma sub_app [c0 c1] (s0 : t c0) (s1 : t c1):
      sub (c0 ++ c1) (app s0 s1) = sub c0 s0 ++ sub c1 s1.
    Proof.
      induction c0.
      - reflexivity.
      - destruct s0 as [[]] using Vector.caseS';
        simpl; f_equal; apply IHc0.
    Qed.

    Lemma map_app [c0 c1] (s0 : t c0) (s1 : t c1) f:
      Vector.map f (app s0 s1) = app (Vector.map f s0) (Vector.map f s1).
    Proof.
      induction c0.
      - reflexivity.
      - destruct s0 using Vector.caseS'.
        simpl; f_equal; apply IHc0.
    Qed.

    Lemma map2_app [c0 c1] (a0 b0 : t c0) (a1 b1 : t c1) f:
      Vector.map2 f (app a0 a1) (app b0 b1) = app (Vector.map2 f a0 b0) (Vector.map2 f a1 b1).
    Proof.
      induction c0.
      - reflexivity.
      - destruct a0 using Vector.caseS'.
        destruct b0 using Vector.caseS'.
        simpl; f_equal; apply IHc0.
    Qed.

    Fixpoint split (c0 c1 : CTX.t) : forall (s : t (c0 ++ c1)), t c0 * t c1.
    Proof.
      case c0 as [|? c0].
      - intro s; split. constructor. exact s.
      - intros [hd tl]%Vector.uncons.
        case (split c0 c1 tl) as (s0, s1).
        exact (Vector.cons _ hd _ s0, s1).
    Defined.
  
    Lemma app_split (c0 c1 : CTX.t) (s : Sub.t (c0 ++ c1)):
      let s01 := Sub.split c0 c1 s in
      s = Sub.app (fst s01) (snd s01).
    Proof.
      induction c0.
      - reflexivity.
      - case s as [hd tl] using Vector.caseS'; simpl.
        specialize (IHc0 tl).
        destruct Sub.split; simpl in *.
        rewrite IHc0; reflexivity.
    Qed.

    Lemma split_app (c0 c1 : CTX.t) (s0 : t c0) (s1 : t c1):
      split c0 c1 (app s0 s1) = (s0, s1).
    Proof.
      induction c0.
      - destruct s0 using Vector.case0. reflexivity.
      - destruct s0 as [? s0] using Vector.caseS'; simpl.
        rewrite (IHc0 s0); reflexivity.
    Qed.


    Fixpoint push [c : CTX.t] : forall (s0 : t c), t c -> t (sub c s0).
    Proof.
      case c as [|c0 c].
      - intros ? _; apply Vector.nil.
      - intro s0.
        case s0 as [hd0 tl0] using Vector.caseS'.
        intros [hd1 tl1]%Vector.uncons.
        pose (tl2 := @push c tl0 tl1).
        case hd0; simpl.
        + exact (Vector.cons _ hd1 _ tl2).
        + exact tl2.
    Defined.

    Lemma push_map [c] (s0 s1 : t c) f:
      push s0 (Vector.map f s1) = Vector.map f (push s0 s1).
    Proof.
      induction c; simpl.
      - reflexivity.
      - destruct s0 as [h ?] using Vector.caseS'; destruct s1 using Vector.caseS'; simpl.
        rewrite IHc.
        case h; reflexivity.
    Qed.

    Lemma sub_push [c] (s0 s1 : t c):
      sub (sub c s0) (push s0 s1) = sub c (and s0 s1).
    Proof.
      induction c; simpl.
      - reflexivity.
      - destruct s0 as [h0 ?] using Vector.caseS'; destruct s1 using Vector.caseS'; simpl.
        case h0; simpl; rewrite IHc; reflexivity.
    Qed.
    
    Fixpoint pull [c : CTX.t] : forall (s0 : t c), t (sub c s0) -> t (sub c (neg s0)) -> t c.
    Proof.
      case c as [|c0 c].
      - intros ? _ _; apply Vector.nil.
      - intro s0.
        case s0 as [hd0 tl0] using Vector.caseS'.
        case hd0; simpl.
        + intros [hd1 tl1]%Vector.uncons s2.
          exact (Vector.cons _ hd1 _ (pull c tl0 tl1 s2)).
        + intros s1 [hd2 tl2]%Vector.uncons.
          exact (Vector.cons _ hd2 _ (pull c tl0 s1 tl2)).
    Defined.

    Lemma map_pull c s0 s1 s2 f:
      Vector.map f (@pull c s0 s1 s2) = pull s0 (Vector.map f s1) (Vector.map f s2).
    Proof.
      induction c as [|c0 c].
      - reflexivity.
      - case s0 as [[] s0] using Vector.caseS'.
        + case s1 as [] using Vector.caseS'; simpl; f_equal; apply IHc.
        + case s2 as [] using Vector.caseS'; simpl; f_equal; apply IHc.
    Qed.

    Lemma sl_pull c s0 s1 s2:
      SLprop.eq (sl (sub c (pull s0 s1 s2)))
                (sl (sub (sub c s0) s1) ** sl (sub (sub c (neg s0)) s2)).
    Proof.
      induction c as [|c0 c].
      - simpl; SLprop.normalize; reflexivity.
      - case s0 as [[] s0] using Vector.caseS'.
        + case s1 as [[]] using Vector.caseS'; simpl;
            rewrite IHc; SLprop.normalize; reflexivity.
        + case s2 as [[]] using Vector.caseS'; simpl;
            rewrite IHc; SLprop.normalize; [rewrite SLprop.star_comm12|]; reflexivity.
    Qed.
  End Sub.

  Definition sub : forall c : t, Sub.t c -> t := Sub.sub.

  Lemma sl_split (c : t) (s : Sub.t c):
    SLprop.eq (sl c) (sl (sub c s) ** sl (sub c (Sub.neg s))).
  Proof.
    induction c; simpl.
    - SLprop.normalize; reflexivity.
    - case s as [hd tl] using Vector.caseS'; simpl.
      rewrite (IHc tl).
      case hd; simpl; SLprop.normalize.
      + reflexivity.
      + apply SLprop.star_comm12.
  Qed.

  Module Inj.
    Local Set Implicit Arguments.

    Record t (c0 c1 : CTX.t) := {
      img : Sub.t c1;
      ieq : SLprop.eq (sl (sub c1 img)) (sl c0);
    }.
  End Inj.
End CTX.

Module VpropList.
  Definition t := list Vprop.t.

  Definition sel : t -> list Type := map Vprop.ty.
  Definition sel_t (vs : t) := Tuple.t (sel vs).

  Fixpoint inst (vs : t) {struct vs} : sel_t vs -> CTX.t :=
    match vs with
    | nil     => fun _ => nil
    | v :: vs => fun '(sel, sels) => existT _ v sel :: inst vs sels
    end.

  Definition of_ctx : CTX.t -> t :=
    map (@projT1 _ _).

  Fixpoint sel_of_ctx (c : CTX.t) : sel_t (of_ctx c) :=
    match c with
    | nil => tt
    | existT _ v s :: c => (s, sel_of_ctx c)
    end.

  Lemma inst_of_ctx ctx:
    inst (of_ctx ctx) (sel_of_ctx ctx) = ctx.
  Proof.
    induction ctx as [|[]]; simpl; f_equal; auto.
  Qed.

  Fixpoint app_sel [vs0 vs1 : t] (ss0 : sel_t vs0) (ss1 : sel_t vs1) : sel_t (vs0 ++ vs1) :=
    match vs0 as vs0 return sel_t vs0 -> sel_t (vs0 ++ vs1) with
    | nil       => fun _ => ss1
    | v0 :: vs0 => fun '(s0, ss0) => (s0, app_sel ss0 ss1)
    end ss0.
  
  Lemma inst_app vs0 vs1 ss0 ss1:
    inst (vs0 ++ vs1) (app_sel ss0 ss1) = inst vs0 ss0 ++ inst vs1 ss1.
  Proof.
    induction vs0; simpl.
    - reflexivity.
    - case ss0 as (s0, ss0); simpl.
      rewrite IHvs0; reflexivity.
  Qed.
End VpropList.

Module _Abbrev.
  Module CP  := SLFun.ConcreteProg.
  Module SP  := SLFun.SLProg.
  Module FP  := SLFun.FunProg.
  Module TF  := FP.TF.
  Module Sub := CTX.Sub.
End _Abbrev.
Import _Abbrev.

Section VProg.
  Context [SIG : sig_context] (SPC : CP.spec_context SIG).

(* [instr] *)

Local Set Implicit Arguments.
Record i_spec_t (A : Type) (ctx : CTX.t) := mk_i_spec {
  sf_csm  : Sub.t ctx;
  sf_prd  : A -> VpropList.t;
  sf_spec : FP.instr (FP.TF.mk_p A (fun x => VpropList.sel (sf_prd x)));
}.
Local Unset Implicit Arguments.

Definition sf_rsel [A ctx] (s : i_spec_t A ctx) (x : A) : list Type :=
  VpropList.sel (sf_prd s x).
Definition sf_rvar [A ctx] (s : i_spec_t A ctx) : TF.p :=
  TF.mk_p A (sf_rsel s).

Definition sf_post_ctx [A ctx] (s : i_spec_t A ctx) (x : A) (sels : VpropList.sel_t (sf_prd s x)) : CTX.t :=
  VpropList.inst (sf_prd s x) sels ++ CTX.sub ctx (Sub.neg (sf_csm s)).

Definition sf_post [A ctx] (s : i_spec_t A ctx) (post : TF.t (sf_rvar s) -> Prop) (x : A) : SLprop.t :=
  SLprop.ex (VpropList.sel_t (sf_prd s x)) (fun sels =>
    SLprop.pure (post (TF.mk (sf_rsel s) x sels)) **
    CTX.sl (sf_post_ctx s x sels))%slprop.

Definition sound_spec [A : Type] (i : @CP.instr SIG A) (ctx : CTX.t) (s : i_spec_t A ctx) : Prop :=
  forall (post : TF.t (sf_rvar s) -> Prop)
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

(* Transformation *)

Section AddCsm.
  Context [A : Type] [ctx : CTX.t] (s : i_spec_t A ctx) (csm : Sub.t ctx).
  
  Let acsm := CTX.sub ctx (Sub.minus csm (sf_csm s)).

  Definition add_csm : i_spec_t A ctx
    :=
    {|
      sf_csm  := Sub.or (sf_csm s) csm;
      sf_prd  := fun x => sf_prd s x ++ VpropList.of_ctx acsm;
      sf_spec := FP.Bind (sf_spec s) (fun x =>
                   FP.Ret (TF.mk _ (TF.v_val x) (VpropList.app_sel (TF.v_sel x) (VpropList.sel_of_ctx acsm)))
                 )
    |}.

  Lemma add_csm_sound (i : @CP.instr SIG A):
    sound_spec i ctx s -> sound_spec i ctx add_csm.
  Proof.
    intros S0 post PRE; simpl in PRE.
    eapply SP.Cons.
    apply S0, PRE.
    split; simpl. reflexivity.
    intro x; unfold add_csm, sf_post, sf_post_ctx, sf_rsel; cbn.
    apply SLprop.imp_exists_l; intro sel0.
    apply SLprop.imp_exists_r with (wit := VpropList.app_sel sel0 (VpropList.sel_of_ctx acsm)).
    apply SLprop.star_morph_imp. reflexivity.
    rewrite VpropList.inst_app, !CTX.sl_app; SLprop.normalize.
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

(* Constructors *)

Section Ret.
  Context [A : Type] (x : A) (sp : A -> list Vprop.t).

  Inductive Ret_Spec (ctx : CTX.t) : i_spec_t A ctx -> Prop
    := Ret_SpecI
    (sels : Tuple.t (map Vprop.ty (sp x)))
    (ij : CTX.Inj.t (VpropList.inst (sp x) sels) ctx) :
    Ret_Spec ctx {|
      sf_csm  := CTX.Inj.img ij;
      sf_prd  := sp;
      sf_spec := FP.Ret (TF.mk (fun x => VpropList.sel (sp x)) x sels);
    |}.

  Program Definition Ret : instr A := {|
    i_impl := CP.Ret x;
    i_spec := fun ctx => Ret_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg (CTX.Inj.img ij)))).
    - apply SP.Ret
       with (sp := fun x' => (SLprop.pure (x' = x) ** CTX.sl (VpropList.inst (sp x) sels))%slprop).
    - split; simpl.
      + SLprop.normalize. apply SLprop.imp_pure_r. reflexivity.
        rewrite CTX.sl_split with (s := CTX.Inj.img ij).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite (CTX.Inj.ieq ij); reflexivity.
      + intro x'. SLprop.normalize. apply SLprop.imp_pure_l. intros ->.
        unfold sf_post; cbn.
        apply SLprop.imp_exists_r with (wit := sels).
        apply SLprop.imp_pure_r. assumption.
        rewrite CTX.sl_app. reflexivity.
  Qed.
End Ret.
Section Bind.
  Context [A B : Type] (f : instr A) (g : A -> instr B).
  
  Local Opaque TF.arrow_ext.

  Inductive Bind_Spec (ctx : CTX.t) : i_spec_t B ctx -> Prop
    := Bind_SpecI : forall
    (s_fp : {s_f : i_spec_t A ctx
                 | proj1_sig (i_spec f ctx) s_f}),
    let s_f := proj1_sig s_fp in
    let f_prd x sels :=
      Sub.app (Sub.const (VpropList.inst (sf_prd s_f x) sels) true)
                  (Sub.const (CTX.sub ctx (Sub.neg (sf_csm s_f))) false)
    in forall
    (s_gp : forall (x : A) (sels : VpropList.sel_t (sf_prd s_f x)),
            let ctx1 := sf_post_ctx s_f x sels in
            {s_g : i_spec_t B ctx1
                 | proj1_sig (i_spec (g x) ctx1) s_g}),
    let s_g := fun x sels => add_csm (proj1_sig (s_gp x sels)) (f_prd x sels)
    in forall
    (csm : Sub.t ctx)
    (CSM : forall x sels,
      Sub.pull (sf_csm s_f) (Sub.const _ true) (snd (Sub.split _ _ (sf_csm (s_g x sels))))
      = csm)
    (prd : B -> VpropList.t)
    (PRD : forall x sels, sf_prd (s_g x sels) = prd),
    Bind_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := prd;
      sf_spec :=
          let TF_A     := TF.mk_p A (sf_rsel s_f) in
          let TF_B prd := TF.mk_p B (fun y => VpropList.sel (prd y)) in
          @FP.Bind TF_A (TF_B prd)
              (sf_spec s_f)
              (TF.arrow_ext TF_A (fun x =>
                eq_rect _ (fun prd => FP.instr (TF_B prd))
                          (sf_spec (s_g (TF.v_val x) (TF.v_sel x)))
                          _ (PRD (TF.v_val x) (TF.v_sel x))))
    |}.
  
  Program Definition Bind : instr B := {|
    i_impl := CP.Bind (i_impl f) (fun x => i_impl (g x));
    i_spec := fun ctx => Bind_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro.
    assert (s_g_sound : forall x sels, sound_spec (i_impl (g x)) _ (s_g x sels)).
      { intros; apply add_csm_sound, (proj2_sig (i_spec (g x) _) _ (proj2_sig (s_gp x sels))). }
    assert (s_g_csm : forall x sels, exists csm,
        sf_csm (s_g x sels) = Sub.app (Sub.const _ true) csm). {
      intros; exists (snd (Sub.split _ _ (sf_csm (proj1_sig (s_gp x sels))))).
      unfold s_g, f_prd; simpl; clear.
      rewrite (Sub.app_split _ _ (sf_csm (proj1_sig (s_gp x sels)))) at 1.
      unfold Sub.const, Sub.or.
      etransitivity. apply Sub.map2_app.
      f_equal; apply Vector.ext; intro k;
        erewrite Vector.nth_map2, !Vector.const_nth by reflexivity;
        destruct (Vector.nth _ k); reflexivity.
    }
    clearbody s_g; clear s_gp.
    eapply SP.Bind.
    - apply (proj2_sig (i_spec f ctx) _ (proj2_sig s_fp)).
      simpl in PRE; apply PRE.
    - clear PRE.
      intro x; unfold sf_post; simpl.
      apply SP.ExistsE; intro sels0.
      apply SP.PureE; rewrite TF.arrow_ext_id; simpl; intro PRE.
      destruct (PRD x sels0); simpl in PRE.
      eapply SP.Cons.
        { apply s_g_sound, PRE. }
      clear PRE.
      split. reflexivity.
      intro y; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      apply SLprop.imp_exists_l; intro sels1.
      apply SLprop.imp_pure_l; intro POST.
      apply SLprop.imp_exists_r with (wit := sels1).
      apply SLprop.imp_pure_r. exact POST.
      rewrite <- (CSM x sels0).
      ecase s_g_csm as [g_csm E]. unfold sf_post_ctx in *; erewrite E.
      clear.
      rewrite !CTX.sl_app. apply SLprop.star_morph_imp. reflexivity.
      rewrite Sub.split_app; simpl.
      unfold Sub.neg, Sub.const.
      rewrite Sub.map_app, Sub.sub_app, Sub.map_pull, !Vector.map_const; simpl.
      rewrite Sub.sl_pull.
      rewrite !Sub.sub_const_false; simpl; SLprop.normalize; reflexivity.
  Qed.
End Bind.
Section Assert.
  Context (A : list Type) (P : Tuple.t A -> CTX.t * Prop).

  Inductive Assert_Spec (ctx : CTX.t) : i_spec_t unit ctx -> Prop
    := Assert_SpecI
    (p : Tuple.t A)
    (ij : CTX.Inj.t (fst (P p)) ctx):
    Assert_Spec ctx {|
      sf_csm  := Sub.const ctx false;
      sf_prd  := fun _ => nil;
      sf_spec := FP.Assert (snd (P p))
    |}.
  
  Program Definition Assert : instr unit := {|
    i_impl := SP.sl_assert (SLprop.ex (Tuple.t A) (fun p =>
                SLprop.pure (snd (P p)) ** CTX.sl (fst (P p))))%slprop;
    i_spec := fun ctx => Assert_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    case PRE as (PRE & POST).
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg (CTX.Inj.img ij)))).
    - apply SP.Assert_imp with (Q := CTX.sl (fst (P p))).
      apply SLprop.imp_exists_r with (wit := p).
      apply SLprop.imp_pure_r. exact PRE.
      reflexivity.
    - eenough (SLprop.eq (CTX.sl ctx) _) as sl_eq.
      split; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      + rewrite sl_eq; reflexivity.
      + intros []; SLprop.normalize.
        apply SLprop.imp_exists_r with (wit := tt).
        apply SLprop.imp_pure_r. exact POST.
        unfold Sub.neg, Sub.const; rewrite Vector.map_const; simpl.
        rewrite Sub.sub_const_true.
        rewrite sl_eq; reflexivity.
      + rewrite CTX.sl_split with (s := CTX.Inj.img ij).
        setoid_rewrite (CTX.Inj.ieq ij).
        reflexivity.
  Qed.
End Assert.
Section Read.
  Context (p : ptr).

  Inductive Read_Spec (ctx : CTX.t) : i_spec_t memdata ctx -> Prop
    := Read_SpecI
    (d : memdata)
    (ij : CTX.Inj.t [CTX.mka (SLprop.cell p, d)] ctx):
    Read_Spec ctx {|
      sf_csm  := Sub.const ctx false;
      sf_prd  := fun _ => nil;
      sf_spec := FP.Ret (TF.mk (fun _ => nil) d tt);
    |}.

  Program Definition Read : instr memdata := {|
    i_impl := CP.Read p;
    i_spec := fun ctx => Read_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg (CTX.Inj.img ij)))).
    - eapply SP.Read with (d := d).
    - eassert (IEq : SLprop.eq _ _). {
        etransitivity. apply (CTX.Inj.ieq ij).
        simpl; SLprop.normalize.
      }
      split; simpl.
      + rewrite CTX.sl_split with (s := CTX.Inj.img ij).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite IEq; reflexivity.
      + intro x'. SLprop.normalize. apply SLprop.imp_pure_l. intros ->.
        unfold sf_post; simpl; SLprop.normalize.
        apply SLprop.imp_exists_r with (wit := tt).
        apply SLprop.imp_pure_r. assumption.
        etransitivity. apply SLprop.star_morph_imp. 2:reflexivity. 
        eapply SLprop.imp_morph. symmetry in IEq; exact IEq. 1,2:reflexivity.
        rewrite <- CTX.sl_split.
        unfold Sub.neg, Sub.const; rewrite Vector.map_const; simpl.
        rewrite Sub.sub_const_true.
        reflexivity.
  Qed.
End Read.
Section Write.
  Context (p : ptr) (d : memdata).

  Inductive Write_Spec (ctx : CTX.t) : i_spec_t unit ctx -> Prop
    := Write_SpecI
    (d0 : memdata)
    (ij : CTX.Inj.t [CTX.mka (SLprop.cell p, d0)] ctx):
    Write_Spec ctx {|
      sf_csm  := CTX.Inj.img ij;
      sf_prd  := fun _ => [Vprop.mk (SLprop.cell p)];
      sf_spec := FP.Ret (TF.mk (fun _ => [memdata]) tt (d, tt));
    |}.

  Program Definition Write : instr unit := {|
    i_impl := CP.Write p d;
    i_spec := fun ctx => Write_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg (CTX.Inj.img ij)))).
    - eapply SP.Write with (d0 := d0).
    - split; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      + rewrite CTX.sl_split with (s := CTX.Inj.img ij).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite (CTX.Inj.ieq ij); simpl; SLprop.normalize; reflexivity.
      + intros []; SLprop.normalize.
        apply SLprop.imp_exists_r with (wit := (d, tt)).
        apply SLprop.imp_pure_r. assumption.
        reflexivity.
  Qed.
End Write.

End VProg.
