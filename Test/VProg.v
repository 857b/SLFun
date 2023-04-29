Require Import SLFun.Util SLFun.Values SLFun.SL.
Require Import SLFun.VProg.

Require Import Coq.Lists.List.

Import SLNotations.
Import ListNotations.
Import VProg._Abbrev.


Definition f_0 : fid := 0.
Definition f_1 : fid := 0.
Definition f_2 : fid := 2.

Definition sig_0 := mk_f_sig (ptr * ptr) unit.
Definition sig_1 := mk_f_sig (ptr * ptr * ptr) unit.
Definition sig_2 := mk_f_sig (ptr * ptr * ptr) ptr.

Definition SIG : sig_context :=
  fun f => match f with
  | 0 => Some sig_0
  | 1 => Some sig_1
  | 2 => Some sig_2
  | _ => None
  end.

Definition spec_0 : FSpec sig_0 (fun '(p0, p1) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1) =>
  Spec.Expanded.mk_r1 [] [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun _ =>
  Spec.Expanded.mk_r2 (fun 'tt =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p0, n1); CTX.mka (SLprop.cell p1, n0)] True)))).
Proof. Tac.build_FSpec. Defined.

Definition spec_1 : FSpec sig_1 (fun '(p0, p1, p2) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1, n2) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p2, n2)]
    [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun _ =>
  Spec.Expanded.mk_r2 (fun 'tt =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p0, n1); CTX.mka (SLprop.cell p1, n0)] True)))).
Proof. Tac.build_FSpec. Defined.

Definition spec_2 : FSpec sig_2 (fun '(p0, p1, p2) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1, n2) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p2, n2)]
             [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun p =>
  Spec.Expanded.mk_r2 (fun '(n, n1') =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p, n); CTX.mka (SLprop.cell p1, n1')] (n1' > 0))))).
Proof.
  Tac.build_FSpec.
Defined.

Definition SPEC : CP.spec_context SIG :=
  fun f => match f with
  | 0 => cp_f_spec (m_spec spec_0)
  | 1 => cp_f_spec (m_spec spec_1)
  | 2 => cp_f_spec (m_spec spec_2)
  | _ => tt
  end.

Definition HSPC_f_0 := cp_has_spec SPEC f_0 eq_refl eq_refl.


Definition vprog_0 : f_body SPEC sig_0 := fun '(p0, p1) =>
  Bind _ (Read  _ p0)    (fun v0 =>
  Bind _ (Read  _ p1)    (fun v1 =>
  Bind _ (Write _ p0 v1) (fun _  =>
         (Write _ p1 v0) ))).

Definition vprog_1 : f_body SPEC sig_1 := fun '(p0, p1, p2) =>
  Call (sg := sig_0) _ f_0 eq_refl (p0, p1) _ (HSPC_f_0 _).

Definition data42 : nat := 42.

Definition vprog_2 : f_body SPEC sig_2 := fun '(p0, p1, p2) =>
  Bind _ (Read  _ p0) (fun v0 =>
  Bind _ (Write _ p1 data42) (fun _ =>
  Bind _ (Assert _ (fun '(v0', v1') =>
    ([CTX.mka (SLprop.cell p0, v0'); CTX.mka (SLprop.cell p1, v1')], v0' = v0))) (fun _ =>
  Ret _ p0 (fun p => [Vprop.mk (SLprop.cell p)])))).

Definition impl_2 (ps : ptr * ptr * ptr) :
  { i : CP.instr ptr | i = i_impl (vprog_2 ps) }.
Proof.
  unfold i_impl, vprog_2; cbn.
  case ps as ((p0, p1), p2); cbn.
  eexists. reflexivity.
Defined.

Lemma imatch_0:
  f_body_match SPEC vprog_0 (m_spec spec_0).
Proof.
  intros (p0, p1).
  Tac.build_impl_match.
  FP.by_wlp.
  tauto.
Qed.

Definition cp_0: f_impl _ vprog_0.
Proof. Tac.extract_impl. Defined.

Lemma imatch_1:
  f_body_match SPEC vprog_1 (m_spec spec_1).
Proof.
  intros ((p0, p1), p2).
  Tac.build_impl_match.
  FP.by_wlp.
  tauto.
Qed.

Definition cp_1: f_impl _ vprog_1.
Proof. Tac.extract_impl. Defined.

Lemma imatch_2:
  f_body_match SPEC vprog_2 (m_spec spec_2).
Proof.
  intros ((p0, p1), p2).
  Tac.build_impl_match.
  FP.by_wlp.
  intuition.
  unfold data42; repeat constructor.
Qed.

Definition cp_2: f_impl _ vprog_2.
Proof. Tac.extract_impl. Defined.


Definition sig_a0 := mk_f_sig (ptr * ptr) unit.
Definition spec_a0 : FSpec sig_a0 (fun ps =>
  Spec.Expanded.mk_r0 (fun n =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell (fst ps), n)] [] True (fun _ =>
  Spec.Expanded.mk_r2 (fun 'tt =>
  Spec.Expanded.mk_r3 [] True)))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0 : f_body SPEC sig_a0 := fun ps =>
  Bind _ (let (p0, _) := ps in Read _ p0) (fun v0 =>
  Ret _ tt (fun _ => [])).
Lemma imatch_a0:
  f_body_match SPEC vprog_a0 (m_spec spec_a0).
Proof.
  intro ps.
  Tac.build_impl_match.
  FP.by_wlp.
  cbn. tauto.
Qed.

Definition cp_a0: f_impl _ vprog_a0.
Proof. Tac.extract_impl. Defined.

