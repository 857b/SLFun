From SLFun Require Import Util Values SL VProg.Vprop VProg.Core.
From Coq   Require Import Lists.List.

Import ListNotations SLNotations VProg.Core.Abbrev.
Import SL.Tactics.


Section Read.
  Context [CT : CP.context] (p : ptr).

  Inductive Read_Spec (ctx : CTX.t) : i_spec_t memdata ctx -> Prop
    := Read_SpecI
    (d : memdata)
    (img : Sub.t ctx)
    (ij : CTX.Inj.ieq [CTX.mka (SLprop.cell p, d)] ctx img):
    Read_Spec ctx {|
      sf_csm  := Sub.const ctx false;
      sf_prd  := fun _ => nil;
      sf_spec := FP.Ret (TF.mk _ d Tuple.tt);
    |}.

  Program Definition Read : instr CT memdata := {|
    i_impl := CP.Read p;
    i_spec := fun ctx => Read_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg img))).
    - eapply SP.Read with (d := d).
    - eassert (IEq : SLprop.eq _ _). {
        etransitivity. apply (CTX.Inj.ieqE ij).
        simpl; SL.normalize.
      }
      split; simpl.
      + rewrite CTX.sl_split with (s := img).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite IEq; reflexivity.
      + intro. SL.normalize. Intro ->.
        unfold sf_post; simpl; SL.normalize.
        Apply. assumption.
        etransitivity. apply SLprop.star_morph_imp. 2:reflexivity. 
        eapply SLprop.imp_morph. symmetry in IEq; exact IEq. 1,2:reflexivity.
        rewrite <- CTX.sl_split.
        unfold Sub.neg, Sub.const; rewrite Vector.map_const; simpl.
        rewrite Sub.sub_const_true.
        reflexivity.
  Qed.
End Read.

Local Ltac build_Read :=
  simple refine (@Read_SpecI _ _ _ _ _);
  [ shelve | shelve | (* ij *) CTX.Inj.build ].

Section Write.
  Context [CT : CP.context] (p : ptr) (d : memdata).

  Inductive Write_Spec (ctx : CTX.t) : i_spec_t unit ctx -> Prop
    := Write_SpecI
    (d0 : memdata)
    (csm : Sub.t ctx)
    (ij : CTX.Inj.ieq [CTX.mka (SLprop.cell p, d0)] ctx csm):
    Write_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := fun _ => [Vprop.mk (SLprop.cell p)];
      sf_spec := FP.Ret (TF.mk (fun _ => [memdata]) tt (d, tt));
    |}.

  Program Definition Write : instr CT unit := {|
    i_impl := CP.Write p d;
    i_spec := fun ctx => Write_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg csm))).
    - eapply SP.Write with (d0 := d0).
    - split; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      + rewrite CTX.sl_split with (s := csm).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite (CTX.Inj.ieqE ij); simpl; SL.normalize; reflexivity.
      + intros []; SL.normalize.
        Apply (d, tt).
        Apply. assumption.
        reflexivity.
  Qed.
End Write.

Local Ltac build_Write :=
  simple refine (@Write_SpecI _ _ _ _ _ _);
  [ shelve | shelve | (* ij *) CTX.Inj.build ].

Module Tactics.
  #[export] Hint Extern 1 (Read_Spec    _ _ _) => build_Read   : HasSpecDB.
  #[export] Hint Extern 1 (Write_Spec _ _ _ _) => build_Write  : HasSpecDB.
End Tactics.
Export Tactics.
