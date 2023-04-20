Require Import SLFun.Util SLFun.Values SLFun.SL.
Require Import SLFun.VProg.

Require Import Coq.Lists.List.

Import SLNotations.
Import ListNotations.
Import VProg._Abbrev.


Definition f_main : fid := 0.

Definition sig_main := mk_f_sig (ptr * ptr) ptr.

Definition SIG : sig_context :=
  fun f => match f with
  | 0 => Some sig_main
  | _ => None
  end.

Definition spec_main_n (ps : ptr * ptr) : SP.Spec.t ptr :=
  let (p0, p1) := ps in {|
  SP.Spec.pre  := SLprop.ex nat (fun n0 => SLprop.cell p0 n0) **
                  SLprop.ex nat (fun n1 => SLprop.cell p1 n1);
  SP.Spec.post := fun p => (SLprop.ex nat (fun n => SLprop.cell p n) ** SLprop.True)%slprop;
|}.

Definition spec_main : SP.f_spec sig_main :=
  fun ps s => eq s (spec_main_n ps).

Definition SPEC : CP.spec_context SIG :=
  fun f => match f with
  | 0 => SP.tr_f_spec spec_main
  | _ => tt
  end.

Definition data42 : nat := 42.

Definition vprog_main (ps : ptr * ptr) : instr SPEC ptr :=
  let (p0, p1) := ps in
  Bind _ (Read  _ p0) (fun v0 =>
  Bind _ (Write _ p1 data42) (fun _ =>
  Bind _ (Assert _ [_] (fun '(v1,_) => ([CTX.mka (SLprop.cell p0,  v1)], v1 = v0))) (fun _ =>
  Ret _ p0 (fun p => [Vprop.mk (SLprop.cell p)])))).

Definition impl_main (ps : ptr * ptr) :
  { i : CP.instr ptr | i = i_impl (vprog_main ps) }.
Proof.
  unfold i_impl, vprog_main; cbn.
  case ps as (p, p0); cbn.
  eexists. reflexivity.
Defined.

Lemma sls_main (ps : ptr * ptr):
  SP.sls SPEC (proj1_sig (impl_main ps)) (spec_main_n ps).
Proof.
  case impl_main as [? ->]; simpl.
  case ps as (p0, p1).
  unfold spec_main_n; SP.normalize.
  apply SP.ExistsE; intro v0.
  apply SP.ExistsE; intro v1.
  eapply SP.Cons.
  - eapply (proj2_sig (i_spec (vprog_main _) [CTX.mka (SLprop.cell p0, v0); CTX.mka (SLprop.cell p1, v1)]))
      with (post := fun _ => True).
    + Tac.build_spec.
    (*
    + Tac.build_Bind_init.
      { Tac.build_Read. }
      { Tac.cbn_refl. }
      cbn; repeat intro.
      Tac.build_Bind_init.
      { Tac.build_Write. }
      { Tac.cbn_refl. }
      cbn; repeat intro.
      Tac.build_Bind_init.
      { Tac.build_Assert. }
      { Tac.cbn_refl. }
      cbn; repeat intro.
      { simple refine (@Ret_SpecI _ _ _ _ _ _ _).
        Tuple.build_shape.
        shelve.
        CTX.Inj.build. }
      Tac.cbn_refl. Tac.cbn_refl. Tac.cbn_refl. Tac.cbn_refl.
      Tac.cbn_refl. Tac.cbn_refl. Tac.cbn_refl. Tac.cbn_refl.
      Tac.cbn_refl. Tac.cbn_refl. Tac.cbn_refl. Tac.cbn_refl.
    *)
    + unfold FP.BindA. cbn. auto.
  - cbn.
    split; cbn.
    + SLprop.normalize. reflexivity.
    + clear; intro p.
      apply SLprop.imp_exists_l; intros (v, (?, [])).
      apply SLprop.imp_pure_l;   intros _.
      apply SLprop.imp_exists_r with (wit := v).
      apply SLprop.star_morph_imp.
      reflexivity.
      constructor.
Qed.
