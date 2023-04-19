Require Import SLFun.Util SLFun.Values SLFun.SL.
Require Import SLFun.VProg.
Require SLFun.ConcreteProg SLFun.SLProg.

Require Import Coq.Lists.List.

Module CP := SLFun.ConcreteProg.
Module SP := SLFun.SLProg.

Import SLNotations.
Import ListNotations.


Definition f_main : fid := 0.

Definition sig_main := mk_f_sig (ptr * ptr) unit.

Definition SIG : sig_context :=
  fun f => match f with
  | 0 => Some sig_main
  | _ => None
  end.

Definition spec_main_n (ps : ptr * ptr) : SP.Spec.t unit :=
  let (p0, p1) := ps in {|
  SP.Spec.pre  := SLprop.ex nat (fun n0 => SLprop.cell p0 n0) **
                  SLprop.ex nat (fun n1 => SLprop.cell p1 n1);
  SP.Spec.post := fun _ => SLprop.True;
|}.

Definition spec_main : SP.f_spec sig_main :=
  fun ps s => eq s (spec_main_n ps).

Definition SPEC : CP.spec_context SIG :=
  fun f => match f with
  | 0 => SP.tr_f_spec spec_main
  | _ => tt
  end.

Definition data42 : nat := 42.

Definition vprog_main (ps : ptr * ptr) : instr SPEC unit :=
  let (p0, p1) := ps in
  Bind _ (Read  _ p0) (fun v0 =>
  Bind _ (Write _ p1 data42) (fun _ =>
  Assert _ [_] (fun '(v1,_) => ([CTX.mka (SLprop.cell p0,  v1)], v1 = v0)))).

Definition impl_main (ps : ptr * ptr) :
  { i : CP.instr unit | i = i_impl (vprog_main ps) }.
Proof.
  unfold i_impl, vprog_main; simpl.
  case ps as (p, p0); simpl.
  eexists. reflexivity.
Defined.

Lemma reduce_spec_t [A ctx] [P : i_spec_t A ctx -> Prop] [s0 s1]
  (H : P s0)
  (E : s0 = s1):
  P s1.
Proof.
  rewrite <- E; exact H.
Qed.

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
    + eapply reduce_spec_t. hnf.
      unshelve refine (@Bind_SpecI _ _ _ _ _ _ _ _ _ _ _ _ _). 3,4:shelve.
      1:eexists. 2-5:cbn.
      { eapply reduce_spec_t. hnf.
        unshelve refine (@Read_SpecI _ _ _ _). 1:shelve.
        unshelve eexists. 3:cbn.
        - exact (Vector.cons _ true _ (Vector.cons _ false _ (Vector.nil _))).
        - cbn; SLprop.normalize; reflexivity.
        - cbn; reflexivity. }

      cbn.
      epose (spec_0 := _).
      intros x sls_0; unshelve eexists; case sls_0 as [].
      exact (spec_0 x). unfold spec_0; clear spec_0. 2-4:cbn.
      eapply reduce_spec_t.
      unshelve refine (@Bind_SpecI _ _ _ _ _ _ _ _ _ _ _ _ _). 3,4:shelve.
      1:eexists. 2-5:cbn.
      { eapply reduce_spec_t. hnf.
        unshelve refine (@Write_SpecI _ _ _ _ _). 1:shelve.
        unshelve eexists. 3:cbn.
        - exact (Vector.cons _ false _ (Vector.cons _ true _ (Vector.nil _))).
        - cbn; SLprop.normalize; reflexivity.
        - cbn; reflexivity. }

      cbn.
      epose (spec_1 := ?[spec_1]).
      intros _u sls_1; unshelve eexists; case sls_1 as [sl_1 []].
      exact (spec_1 _u sl_1). unfold spec_1; clear spec_1. 2-4:cbn.
      { eapply reduce_spec_t.
        unshelve refine (@Assert_SpecI _ _ _ _ _).
        1:repeat (constructor; [shelve|]); constructor.
        all:cbn.
        - unshelve eexists.
          + exact (Vector.cons _ false _ (Vector.cons _ true _ (Vector.nil _))).
          + cbn; SLprop.normalize; reflexivity.
        - cbn; reflexivity. }

      intros ? [? []]; cbn; reflexivity.
      intros ? [? []]; cbn; reflexivity.
      unfold _Abbrev.TF.arrow_ext, _Abbrev.TF.arrow_of_fun, sf_rsel; cbn. reflexivity.
      intros ? []; cbn; reflexivity.
      intros ? []; cbn; reflexivity.
      unfold _Abbrev.TF.arrow_ext, _Abbrev.TF.arrow_of_fun, sf_rsel; cbn. reflexivity.
    + cbn. auto.
  - unfold sf_post, sf_post_ctx; cbn.
    split; cbn.
    + SLprop.normalize. reflexivity.
    + constructor.
Qed.
