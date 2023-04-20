Require Import SLFun.Util SLFun.Values SLFun.SL.
Require Import SLFun.VProg.

Require Import Coq.Lists.List.

Import SLNotations.
Import ListNotations.
Import VProg._Abbrev.


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
    + simple refine (Bind_SpecI1 _ _ _ _ _ _ _ _ _ _). 1,3,5,7,9,11,13:shelve.
      { hnf.
        simple refine (@Read_SpecI _ _ _ _). 1:shelve.
        unshelve eexists.
        - exact (Vector.cons _ true _ (Vector.cons _ false _ (Vector.nil _))).
        - cbn; SLprop.normalize; reflexivity. }
      { cbn; repeat intro. reflexivity. }
      cbn; repeat intro.
      simple refine (Bind_SpecI1 _ _ _ _ _ _ _ _ _ _). 1,3,5,7,9,11,13:shelve.
      { unshelve refine (@Write_SpecI _ _ _ _ _). 1:shelve.
        unshelve eexists.
        - exact (Vector.cons _ false _ (Vector.cons _ true _ (Vector.nil _))).
        - cbn; SLprop.normalize; reflexivity. }
      { cbn; repeat intro. reflexivity. }
      cbn; repeat intro.
      { unshelve refine (@Assert_SpecI _ _ _ _ _).
        1:repeat (constructor; [shelve|]); constructor.
        cbn.
        unshelve eexists.
        - exact (Vector.cons _ false _ (Vector.cons _ true _ (Vector.nil _))).
        - cbn; SLprop.normalize; reflexivity. }
      { cbn; repeat intro. reflexivity. }
      { cbn; repeat intro. reflexivity. }
      { cbn; repeat intro. reflexivity. }
      { cbn; repeat intro. reflexivity. }
      { cbn; repeat intro. reflexivity. }
      { cbn; repeat intro. reflexivity. }
      { cbn; repeat intro. reflexivity. }
      { cbn; repeat intro. reflexivity. }
    + unfold FP.BindA. cbn. auto.
  - cbn.
    split; cbn.
    + SLprop.normalize. reflexivity.
    + constructor.
Qed.
