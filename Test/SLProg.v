From SLFun Require Import Util SLProg SL.

Import SLNotations SLProg.Tactics.


Definition f_aux  : fid := 0.
Definition f_main : fid := 1.

Definition sig_aux  := mk_f_sig ptr nat.
Definition sig_main := mk_f_sig (ptr * ptr) unit.

Definition SIG : sig_context :=
  fun f => match f with
  | 0 => Some sig_aux
  | 1 => Some sig_main
  | _ => None
  end.

Definition spec_aux_n (p : ptr) (n : nat) : Spec.t nat := {|
  Spec.pre  := SLprop.cell p n;
  Spec.post := fun m => SLprop.cell p (n + m);
|}.

Definition spec_aux : FSpec.t sig_aux :=
  fun p s => exists (n : nat), eq s (spec_aux_n p n).

Definition spec_main_n (ps : ptr * ptr) : Spec.t unit :=
  let (p0, p1) := ps in {|
  Spec.pre  := SLprop.ex nat (fun n0 => SLprop.cell p0 n0) **
               SLprop.ex nat (fun n1 => SLprop.cell p1 n1);
  Spec.post := fun _ => SLprop.True;
|}.

Definition spec_main : FSpec.t sig_main :=
  fun ps s => eq s (spec_main_n ps).

Definition SPEC : CP.spec_context SIG :=
  fun f => match f with
  | 0 => FSpec.tr spec_aux
  | 1 => FSpec.tr spec_main
  | _ => tt
  end.

Lemma call_aux (p : ptr) (n : nat):
  @fun_has_spec _ SPEC sig_aux (CP.mk_f_sigh _ None None) f_aux eq_refl p (spec_aux_n p n).
Proof.
  unfold fun_has_spec; rewrite Spec.spec_match_iff; cbn.
  intros s TR.
  apply CP.fun_has_spec_no_ghost2 with (sg := sig_aux).
  cbn; unfold spec_aux.
  do 2 esplit; eauto.
Defined.

Definition impl_aux (p : ptr) : @CP.instr SIG nat :=
  CP.Bind (CP.Read p) (fun n =>
  CP.Bind (CP.Write p (n + 2)) (fun _ =>
  CP.Ret 2)).

Lemma sls_aux (p : ptr) (n : nat) : sls SPEC (impl_aux p) (spec_aux_n p n).
Proof.
  eapply Bind. eapply Read. intro n'; SL.normalize.
  apply PureE; intros ->.
  eapply Bind. eapply Write. intro _u.
  eapply Ret_SL with (sp := fun r => SLprop.cell p (n + r)).
Qed.

Definition impl_main (ps : ptr * ptr) : @CP.instr SIG unit :=
  let (p0, p1) := ps in
  CP.Bind (CP.Read p1) (fun n1 =>
  CP.Bind (CP.Call_gh (CP.mk_f_sigh sig_aux None None) f_aux eq_refl p0) (fun m =>
  CP.Bind (CP.Read p1) (fun n1' =>
  sl_assert (SLprop.pure (n1 = n1'))))).

Lemma sls_main ps : sls SPEC (impl_main ps) (spec_main_n ps).
Proof.
  case ps as (p0, p1); simpl.
  normalize.
  eapply ExistsE; intro n0.
  eapply ExistsE; intro n1.
  eapply Bind.
    eapply CFrame with (fr := SLprop.cell p0 n0).
    eapply Read.
    simpl. rewrite SLprop.star_comm. reflexivityR.
  intro; simpl; normalize; apply PureE; intros ->.
  eapply Bind.
    eapply CFrame with (fr := SLprop.cell p1 n1).
    apply (Call _ _ _ _ _ _ (call_aux p0 n0)).
    rewrite SLprop.star_comm; reflexivityR.
  intro m; simpl.
  eapply Bind.
    eapply CFrame with (fr := SLprop.cell p0 (n0 + m)).
    eapply Read.
    simpl. rewrite SLprop.star_comm. reflexivityR.
  intro n1'; simpl; normalize; apply PureE; intros ->.
    eapply CFrame.
    apply Assert.
  split; simpl.
  - apply SLprop.imp_pure_r; reflexivity.
  - constructor.
Qed.

Definition IMPL : CP.impl_context SIG :=
  fun f => match f with
  | 0 => impl_aux
  | 1 => impl_main
  | _ => tt
  end.

Lemma match_context:
  CP.context_match_spec IMPL SPEC.
Proof.
  intros [|[|]]; simpl. 3:constructor.
  - intros p t_s (s_s & [n ->] & TR).
    eapply sls_impl_tr, TR.
    apply sls_aux.
  - intros ps t_s (s_s & -> & TR).
    eapply sls_impl_tr, TR.
    apply sls_main.
Qed.

Lemma context_oracle_free:
  CP.context_oracle_free IMPL.
Proof.
  intros [|[|]]; simpl; repeat constructor.
  (* intro. set (imp := impl_main x); hnf in imp; subst imp. *)
  intros (?,?); simpl; repeat constructor.
Qed.

Lemma main_okstate m p0 p1 s'
  (NN_P0  : p0 <> NULL) (NN_P1  : p1 <> NULL)
  (NALIAS : p0 <> p1)
  (STEPS  : CP.steps IMPL (m, CP.get_fun_body IMPL f_main eq_refl (p0, p1)) s'):
  CP.okstate IMPL s'.
Proof.
  eapply CP.func_okstate in STEPS; eauto using match_context, context_oracle_free.
  { cbn; do 2 esplit. reflexivity.
    exists SLprop.True; reflexivity. }
  cbn.
  eexists (FMem.of_mem m); split. apply FMem.match_of_mem.
  exists (fun p => UPred.one (if Mem.ptr_eq p p0 then Some (m p0)
                         else if Mem.ptr_eq p p1 then Some (m p1)
                            else None)),
         (fun p => UPred.one (if Mem.ptr_eq p p0 then None
                         else if Mem.ptr_eq p p1 then None
                            else Some (m p))).
  split. {
    intro p; unfold FMem.of_mem; repeat setoid_rewrite UPred.bind_one.
    repeat case Mem.ptr_eq as []; subst; constructor.
  }
  split.
  - eexists _, _; split; [|split; (do 2 esplit; [assumption|reflexivity])].
    intro p; unfold FMem.cell;
    do 2 case Mem.ptr_eq as [|]; subst; try congruence;
    repeat setoid_rewrite UPred.bind_one;
    constructor.
  - constructor.
Qed.
