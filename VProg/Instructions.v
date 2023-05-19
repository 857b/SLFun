From SLFun Require Import Util Values SL VProg.Vprop VProg.Core.
From Coq   Require Import Lists.List.

Import ListNotations SLNotations VProg.Core.Abbrev.
Import SL.Tactics.


Section Read.
  Context [CT : CP.context] (p : ptr).

  Inductive Read_Spec (ctx : CTX.t) (F : i_spec_t memdata ctx) : Prop
    := Read_SpecI
    (d : memdata)
    (IJ : InjPre_Frame_Spec [CTX.mka (SLprop.cell p, d)] ctx {|
      sf_csm  := Vector.cons _ false _ (Vector.nil _) <: Sub.t [_];
      sf_prd  := fun _ => nil;
      sf_spec := FP.Ret (TF.mk _ d Tuple.tt);
    |} F).

  Program Definition Read : instr CT memdata := {|
    i_impl := CP.Read p;
    i_spec := fun ctx => Read_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_Frame IJ); clear IJ.
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
  simple refine (Read_SpecI _ _ _ _ _);
  [ shelve | (*IJ *) Tac.build_InjPre_Frame; Tac.cbn_refl ].

Section Write.
  Context [CT : CP.context] (p : ptr) (d : memdata).

  Inductive Write_Spec (ctx : CTX.t) (F : i_spec_t unit ctx) : Prop
    := Write_SpecI
    (d0 : memdata)
    (IJ : InjPre_Frame_Spec [CTX.mka (SLprop.cell p, d0)] ctx {|
      sf_csm  := Vector.cons _ true _ (Vector.nil _) <: Sub.t [_];
      sf_prd  := fun _ => [Vprop.mk (SLprop.cell p)];
      sf_spec := FP.Ret (TF.mk (fun _ => [memdata]) tt (d, tt));
    |} F).

  Program Definition Write : instr CT unit := {|
    i_impl := CP.Write p d;
    i_spec := fun ctx => Write_Spec ctx;
  |}.
  Next Obligation.
    destruct SP.
    apply (Tr_InjPre_Frame IJ); clear IJ.
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
  simple refine (Write_SpecI _ _ _ _ _ _);
  [ shelve | (* IJ *) Tac.build_InjPre_Frame; Tac.cbn_refl ].

Module Tactics.
  #[export] Hint Extern 1 (Read_Spec    _ _ _) => build_Read   : HasSpecDB.
  #[export] Hint Extern 1 (Write_Spec _ _ _ _) => build_Write  : HasSpecDB.
End Tactics.
Export Tactics.
