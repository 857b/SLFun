Require Import SLFun.Util SLFun.Values SLFun.SL.
Require Import SLFun.VProg.

Require Import Coq.Lists.List.

Import SLNotations.
Import ListNotations.
Import DTuple.Notations.
Import VProg._Abbrev.

Definition f_0 : fid := 0.
Definition f_1 : fid := 0.
Definition f_2 : fid := 2.
Definition f_3 : fid := 3.
Definition f_4 : fid := 4.

Definition sig_0 := mk_f_sig (ptr * ptr) unit.
Definition sig_1 := mk_f_sig (ptr * ptr * ptr) unit.
Definition sig_2 := mk_f_sig (ptr * ptr * ptr) ptr.
Definition sig_3 := mk_f_sig ptr ptr.
Definition sig_4 := mk_f_sig (ptr * ptr) ptr.

Definition SIG : sig_context :=
  fun f => match f with
  | 0 => Some sig_0
  | 1 => Some sig_1
  | 2 => Some sig_2
  | 3 => Some sig_3
  | 4 => Some sig_4
  | _ => None
  end.

Definition sigh_0 := mk_f_sigh sig_0 None None.
Definition spec_0 : FSpec sigh_0 (fun '(p0, p1) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1) =>
  Spec.Expanded.mk_r1 [] [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun _ =>
  Spec.Expanded.mk_r2 (fun 'tt =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p0, n1); CTX.mka (SLprop.cell p1, n0)] True)))).
Proof. Tac.build_FSpec. Defined.

Definition sigh_1 := mk_f_sigh sig_1 None None.
Definition spec_1 : FSpec sigh_1 (fun '(p0, p1, p2) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1, n2) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p2, n2)]
    [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun _ =>
  Spec.Expanded.mk_r2 (fun 'tt =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p0, n1); CTX.mka (SLprop.cell p1, n0)] True)))).
Proof. Tac.build_FSpec. Defined.

Definition sigh_2 := mk_f_sigh sig_2 None None.
Definition spec_2 : FSpec sigh_2 (fun '(p0, p1, p2) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1, n2) =>
  Spec.Expanded.mk_r1 (GO := None) [CTX.mka (SLprop.cell p2, n2)]
             [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun p =>
  Spec.Expanded.mk_r2 (fun '(n, n1') =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p, n); CTX.mka (SLprop.cell p1, n1')] (n1' > 0))))).
Proof. Tac.build_FSpec. Defined.

Definition sigh_3 := mk_f_sigh sig_3 (Some (fun _ => ptr)) (Some (fun _ => ptr)).
Definition spec_3 : FSpec sigh_3 (fun p0 p1 =>
  Spec.Expanded.mk_r0 (fun '(n0, n1) =>
  Spec.Expanded.mk_r1 (GO := Some _) []
             [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun r =>
  Spec.Expanded.mk_r2 (fun '(n0', n1') =>
  Spec.Expanded.mk_r3
             [CTX.mka (SLprop.cell (CP.projG1 r), n0'); CTX.mka (SLprop.cell (CP.projG2 r), n1')] True)))).
Proof. Tac.build_FSpec. Defined.

Definition sigh_4 := mk_f_sigh sig_4 None (Some (fun _ => ptr)).
Definition spec_4 : FSpec sigh_4 (fun '(p0, p1) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1) =>
  Spec.Expanded.mk_r1 (GO := Some _) []
             [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun r =>
  Spec.Expanded.mk_r2 (fun '(n0', n1') =>
  Spec.Expanded.mk_r3
             [CTX.mka (SLprop.cell (CP.projG1 r), n0'); CTX.mka (SLprop.cell (CP.projG2 r), n1')] True)))).
Proof. Tac.build_FSpec. Defined.

Definition SPEC : CP.spec_context SIG :=
  fun f => match f with
  | 0 => cp_f_spec (m_spec spec_0)
  | 1 => cp_f_spec (m_spec spec_1)
  | 2 => cp_f_spec (m_spec spec_2)
  | 3 => cp_f_spec (m_spec spec_3)
  | 4 => cp_f_spec (m_spec spec_4)
  | _ => tt
  end.

Definition HSPC_f_0 := cp_has_spec SPEC f_0 eq_refl eq_refl.
Definition HSPC_f_3 := cp_has_spec SPEC f_3 eq_refl eq_refl.


Definition vprog_0 : f_body SPEC sigh_0 := fun '(p0, p1) =>
  Bind _ (Read  _ p0)    (fun v0 =>
  Bind _ (Read  _ p1)    (fun v1 =>
  Bind _ (Write _ p0 v1) (fun _  =>
         (Write _ p1 v0) ))).

Definition vprog_1 : f_body SPEC sigh_1 := fun '(p0, p1, p2) =>
  Call _ f_0 eq_refl sigh_0 (p0, p1) tt _ (HSPC_f_0 _).

Definition data42 : nat := 42.

Definition vprog_2 : f_body SPEC sigh_2 := fun '(p0, p1, p2) =>
  Bind _ (Read  _ p0) (fun v0 =>
  Bind _ (Write _ p1 data42) (fun _ =>
  Bind _ (Assert _ (fun '(v0', v1') =>
    ([CTX.mka (SLprop.cell p0, v0'); CTX.mka (SLprop.cell p1, v1')], v0' = v0))) (fun _ =>
  Ret _ p0 (fun p => [Vprop.mk (SLprop.cell p)])))).

Definition vprog_3 : f_body SPEC sigh_3 := fun p0 p1 =>
  Ret _ (CP.existG _ p0 p1)
        (fun r => [Vprop.mk (SLprop.cell (CP.projG1 r)); Vprop.mk (SLprop.cell (CP.projG2 r))]).

Definition vprog_4 : f_body SPEC sigh_4 := fun '(p0, p1) =>
  Bind _ (Call _ f_3 eq_refl sigh_3 p0 p1 _ (HSPC_f_3 _)) (fun '(CP.existG _ p0' p1') =>
  Ret _ (CP.existG _ p0' p1')
        (fun r => [Vprop.mk (SLprop.cell (CP.projG1 r)); Vprop.mk (SLprop.cell (CP.projG2 r))])).


Lemma imatch_0:
  f_body_match vprog_0 (m_spec spec_0).
Proof.
  intros (p0, p1).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  tauto.
Qed.

Definition cp_0: f_impl vprog_0.
Proof. Tac.extract_impl. Defined.


Lemma imatch_1:
  f_body_match vprog_1 (m_spec spec_1).
Proof.
  intros ((p0, p1), p2).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  tauto.
Qed.

Definition cp_1: f_impl vprog_1.
Proof. Tac.extract_impl. Defined.

Lemma imatch_2:
  f_body_match vprog_2 (m_spec spec_2).
Proof.
  intros ((p0, p1), p2).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition.
  unfold data42; repeat constructor.
Qed.

Definition cp_2: f_impl vprog_2.
Proof. Tac.extract_impl. Defined.


Lemma imatch_3:
  f_body_match vprog_3 (m_spec spec_3).
Proof.
  intros p0.
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  tauto.
Qed.

Definition cp_3: f_impl vprog_3.
Proof. Tac.extract_impl. Defined.

Lemma imatch_4:
  f_body_match vprog_4 (m_spec spec_4).
Proof.
  intros (p0, p1).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  tauto.
Qed.

Definition cp_4: f_impl vprog_4.
Proof. Tac.extract_impl. Defined.


Definition IMPL : CP.impl_context SIG :=
  fun f => match f with
  | 0 => proj1_sig cp_0
  | 1 => proj1_sig cp_1
  | 2 => proj1_sig cp_2
  | 3 => proj1_sig cp_3
  | 4 => proj1_sig cp_4
  | _ => tt
  end.

Ltac case_until_True :=
  try exact (fun _ => Logic.I);
  let i := fresh "i" in
  intros [|i]; [|revert i; case_until_True].

Lemma match_context:
  CP.context_match_spec IMPL SPEC.
Proof.
  case_until_True;
  cbn beta iota delta [SIG IMPL SPEC];
  apply f_impl_match_spec.
  - apply imatch_0.
  - apply imatch_1.
  - apply imatch_2.
  - apply imatch_3.
  - apply imatch_4.
Qed.

Lemma context_oracle_free:
  CP.context_oracle_free IMPL.
Proof.
  case_until_True;
  cbn beta iota delta [SIG IMPL SPEC];
  apply f_impl_oracle_free.
Qed.


Definition sigh_a0 := mk_f_sig1 (ptr * ptr) None unit None.
Definition spec_a0 : FSpec sigh_a0 (fun ps =>
  Spec.Expanded.mk_r0 (fun n =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell (fst ps), n)] [] True (fun _ =>
  Spec.Expanded.mk_r2 (fun 'tt =>
  Spec.Expanded.mk_r3 [] True)))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0 : f_body SPEC sigh_a0 := fun ps =>
  Bind _ (let (p0, _) := ps in Read _ p0) (fun v0 =>
  Ret _ tt (fun _ => [])).
Lemma imatch_a0:
  f_body_match vprog_a0 (m_spec spec_a0).
Proof.
  intro ps.
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  cbn. tauto.
Qed.

Definition cp_a0: f_impl vprog_a0.
Proof. Tac.extract_impl. Defined.


Definition sigh_a1a := mk_f_sig1 (bool * ptr * ptr * ptr) None unit None.
Definition spec_a1a : FSpec sigh_a1a (fun '(b, p0, p1, p2) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1, n2) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p0, n0)] [CTX.mka (SLprop.cell p1, n1); CTX.mka (SLprop.cell p2, n2)]
    True (fun _ =>
  Spec.Expanded.mk_r2 (fun '(n1', n2') =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p1, n1'); CTX.mka (SLprop.cell p2, n2')]
    (b = true -> n1' = 0))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1a : f_body SPEC sigh_a1a := fun '(b, p0, p1, p2) =>
  if b
  then Write _ p1 0
  else Write _ p2 1.
Lemma imatch_a1a:
  f_body_match vprog_a1a (m_spec spec_a1a).
Proof.
  intros (((b, p0), p1), p2).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition congruence.
Qed.

Definition cp_a1a: f_impl vprog_a1a.
Proof. Tac.extract_impl. Defined.


Inductive bool3 : Set := B0 | B1 | B2.

Definition sigh_a1b := mk_f_sig1 (bool3 * ptr) None unit None.
Definition spec_a1b : FSpec sigh_a1b (fun '(b, p) =>
  Spec.Expanded.mk_r0 (fun n =>
  Spec.Expanded.mk_r1 [] [CTX.mka (SLprop.cell p, n)] (b <> B2) (fun _ =>
  Spec.Expanded.mk_r2 (fun n' =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p, n')] (b <> B1 -> n' = 0))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1b : f_body SPEC sigh_a1b := fun '(b, p) =>
  match b with
  | B0 => Write _ p 0
  | B1 | B2 => Ret _ tt (fun _ => [])
  end.
Lemma imatch_a1b:
  f_body_match vprog_a1b (m_spec spec_a1b).
Proof.
  intros (b, p).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition congruence.
Qed.


Definition sigh_a1c := mk_f_sig1 (option nat * ptr) None unit None.
Definition spec_a1c : FSpec sigh_a1c (fun '(o, p) =>
  Spec.Expanded.mk_r0 (fun n =>
  Spec.Expanded.mk_r1 [] [CTX.mka (SLprop.cell p, n)]
    (n > 0 /\ match o with Some n' => n' > 0 | None => True end) (fun _ =>
  Spec.Expanded.mk_r2 (fun n' =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p, n')] (n' > 0))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1c : f_body SPEC sigh_a1c := fun '(o, p) =>
  match o with
  | Some n => Write _ p n
  | None   => Ret _ tt (fun _ => [])
  end.
Lemma imatch_a1c:
  f_body_match vprog_a1c (m_spec spec_a1c).
Proof.
  intros (o, p).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp_ false.
  destruct o; tauto.
Qed.


Definition sigh_a2a := mk_f_sig1 (ptr * ptr) None unit None.
Definition spec_a2a : FSpec sigh_a2a (fun '(p0, p1) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p0, n0)] [CTX.mka (SLprop.cell p1, n1)]
    (n0 <= n1) (fun _ =>
  Spec.Expanded.mk_r2 (fun n1' =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p1, n1')] (n0 <= n1'))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a2a : f_body SPEC sigh_a2a := fun '(p0, p1) =>
  Bind _ (Read _ p1) (fun v1 =>
  Bind _ (GGet _ (SLprop.cell p0)) (fun v0 =>
  Bind _ (Assert _ (fun 'tt => ([], v0 <= v1))) (fun _ =>
          Write _ p1 (S v1)))).
Lemma imatch_a2a:
  f_body_match vprog_a2a (m_spec spec_a2a).
Proof.
  intros (p0, p1).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition.
Qed.
Definition cp_a2a: f_impl vprog_a2a.
Proof. Tac.extract_impl. Defined.

Definition vprog_a2b : f_body SPEC sigh_a2a := fun '(p0, p1) =>
  Bind _ (Bind _ (Read _ p1) (fun v1 =>
          Bind _ (GGet _ (SLprop.cell p0)) (fun v0 =>
          Ret _ (CP.existG _ v1 v0) (fun _ => [])))) (fun '(CP.existG _ v1 v0) =>
  Bind _ (Assert _ (fun 'tt => ([], v0 <= v1))) (fun _ =>
          Write _ p1 (S v1))).
Lemma imatch_a2b:
  f_body_match vprog_a2b (m_spec spec_a2a).
Proof.
  intros (p0, p1).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition.
Qed.
Definition cp_a2b: f_impl vprog_a2b.
Proof. Tac.extract_impl. Defined.


Definition sigh_a3 := mk_f_sig1 unit (Some (fun _ => (nat * nat)%type <: Type)) unit (Some (fun _ => nat <: Type)).
Definition spec_a3 : FSpec sigh_a3 (fun _ '(n0, n1) =>
  Spec.Expanded.mk_r0 (fun 'tt =>
  Spec.Expanded.mk_r1 (GO := Some _) [] [] True (fun r =>
  Spec.Expanded.mk_r2 (fun 'tt =>
  Spec.Expanded.mk_r3 [] (CP.projG2 r = n0 + n1))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a3 : f_body SPEC sigh_a3 := fun _ '(n0, n1) =>
  Ret _ (CP.existG _ tt (n0 + n1)) (fun _ => []).
Lemma imatch_a3:
  f_body_match vprog_a3 (m_spec spec_a3).
Proof.
  intros _arg.
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  tauto.
Qed.
Definition cp_a3: f_impl vprog_a3.
Proof. Tac.extract_impl. Defined.
