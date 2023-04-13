Require Import SLFun.Util.
Require Import SLFun.SLProg.
Require Import SLFun.SL.

Import SLNotations.


Definition f_aux  : CP.fid := 0.
Definition f_main : CP.fid := 1.

Definition sig_aux  := CP.mk_f_sig ptr nat.
Definition sig_main := CP.mk_f_sig (ptr * ptr) unit.

Definition SIG : CP.sig_context :=
  fun f => match f with
  | 0 => Some sig_aux
  | 1 => Some sig_main
  | _ => None
  end.

Definition spec_aux_n (p : ptr) (n : nat) : Spec.t nat := {|
  Spec.pre  := SLprop.cell p n;
  Spec.post := fun m => SLprop.cell p (n + m);
|}.

Definition spec_aux : f_spec sig_aux :=
  fun p s => exists (n : nat), eq s (spec_aux_n p n).

Definition spec_main_n (ps : ptr * ptr) : Spec.t unit := {|
  Spec.pre  := SLprop.cell (fst ps) 0 ** SLprop.cell (snd ps) 0;
  Spec.post := fun _ => SLprop.True;
|}.

Definition spec_main : f_spec sig_main :=
  fun ps s => eq s (spec_main_n ps).

Definition SPEC : CP.spec_context SIG :=
  fun f => match f with
  | 0 => tr_f_spec spec_aux
  | 1 => tr_f_spec spec_main
  | _ => tt
  end.

Lemma call_aux (p : ptr) (n : nat):
  @fun_has_spec _ SPEC sig_aux f_aux p (spec_aux_n p n).
Proof.
  unshelve eexists. reflexivity.
  simpl.
  apply (tr_f_spec_match spec_aux).
  do 2 esplit.
Defined.

Definition impl_aux (p : ptr) : @CP.instr SIG nat :=
  CP.Bind (CP.Read p) (fun n =>
  CP.Bind (CP.Write p (n + 2)) (fun _ =>
  CP.Ret 2)).

Lemma sls_aux (p : ptr) (n : nat) : sls SPEC (impl_aux p) (spec_aux_n p n).
Proof.
  eapply Bind. eapply Read. intro n'.
  eapply Cons. eapply Frame with (fr := SLprop.pure (n' = n)).
  eapply Bind. eapply Write. intro _u.
  eapply Ret with (sp := fun r => SLprop.cell p (n' + r)).
  split; simpl.
  - intros fm H.
    assert (n' = n). {
      case H as (? & ? & ? & ? & H); apply H.
    }
    subst n'; eassumption.
  - intro r.
    rewrite SLprop.star_comm.
    apply SLprop.imp_pure_l.
    intros ->; reflexivity.
Defined.

Definition impl_main (ps : ptr * ptr) : @CP.instr SIG unit :=
  let (p0, p1) := ps in
  CP.Bind (CP.Call (sg := sig_aux) f_aux eq_refl p0) (fun n =>
  CP.Ret tt).

Lemma sls_main ps : sls SPEC (impl_main ps) (spec_main_n ps).
Proof.
  case ps as (p0, p1); simpl.
  eapply Bind.
  eapply Cons. eapply Frame with (fr := SLprop.cell p1 0).
  eapply Call with (fs := call_aux p0 0).
  reflexivityR.
  intros _n.
  eapply Cons. exact (Ret _ tt (fun _ => SLprop.True)).
  split; simpl; constructor.
Defined.

Definition IMPL : CP.impl_context SIG :=
  fun f => match f with
  | 0 => impl_aux
  | 1 => impl_main
  | _ => tt
  end.

Lemma wp_impl_tr_f_spec [sg sp x wp]
  [IM : Spec.wp_match (sp x) wp]
  [s] (TR : @tr_f_spec sg (fun x s => s = sp x) x s):
  CP.Spec.wp_impl wp s.
Proof.
  case TR as (? & fr & ? & ?); subst.
  apply IM.
Qed.

Lemma tr_f_spec_exists A sg sp x s:
  @tr_f_spec sg (fun x s => exists y : A, sp s x y) x s ->
  exists y : A, tr_f_spec (fun x s => sp s x y) x s.
Proof.
  intros (? & fr & (y & ?) & ?); subst.
  eexists y, _, fr; eauto.
Qed.

Lemma match_context:
  CP.context_match_spec IMPL SPEC.
Proof.
  intros [|[|]]; simpl. 3:constructor.
  - intros p s TR.
    apply tr_f_spec_exists in TR as [n TR].
    refine (wp_impl_tr_f_spec TR).
    apply sls_aux.
  - intros ps; apply wp_impl_tr_f_spec.
    apply sls_main.
Qed.

Lemma context_oracle_free:
  CP.context_oracle_free IMPL.
Proof.
  intros [|[|]]; simpl; repeat constructor.
  (* intro. set (imp := impl_main x); hnf in imp; subst imp. *)
  intros (?,?); simpl; repeat constructor.
Qed.
