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
  FP.simpl_prog.
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
  FP.simpl_prog.
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
  FP.simpl_prog.
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
  FP.simpl_prog.
  FP.by_wlp.
  cbn. tauto.
Qed.

Definition cp_a0: f_impl _ vprog_a0.
Proof. Tac.extract_impl. Defined.


Definition sig_a1a := mk_f_sig (bool * ptr * ptr * ptr) unit.
Definition spec_a1a : FSpec sig_a1a (fun '(b, p0, p1, p2) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1, n2) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p0, n0)] [CTX.mka (SLprop.cell p1, n1); CTX.mka (SLprop.cell p2, n2)]
    True (fun _ =>
  Spec.Expanded.mk_r2 (fun '(n1', n2') =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p1, n1'); CTX.mka (SLprop.cell p2, n2')]
    (b = true -> n1' = 0))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1a : f_body SPEC sig_a1a := fun '(b, p0, p1, p2) =>
  if b
  then Write _ p1 0
  else Write _ p2 1.
Lemma imatch_a1a:
  f_body_match SPEC vprog_a1a (m_spec spec_a1a).
Proof.
  intros (((b, p0), p1), p2).
  Tac.build_impl_match.
  (*
  Tac.build_impl_match_init.
  refine (transform_spec _ _ _).
  - Tac.build_HasSpec_branch ltac:(fun _ => Tac.build_HasSpec) b.
    (*
    refine (transform_spec _ _ _).
    + (* For each branch a specification where [sf_csm] and [sf_prd] do not depend on the
         arguments of the matched value. *)
      lazymatch goal with |- HasSpec _ _ _ ?s =>
        Tac.build_term s ltac:(fun _ =>
          simple refine (mk_i_spec _ _ _);
          [ (* sf_csm  *) cbn; Tac.const_case b; clear
          | (* sf_prd  *) cbn; Tac.const_case b; clear b
          | (* sf_spec *) case b; clear b ];
          shelve)
      end;
      cbn.
      case b;
      (simple refine (VProg.Tac.change_arg _ _ _ _);
       [ shelve | Tac.build_HasSpec | Tac.build_i_spec_t_eq ]).
    + cbn.
      simple refine (intro_TrSpec_branch _ _ _ _ _).
      1,2:clear; shelve.
      1:shelve.
      { (* f1 *) Tac.nondep_case b; clear b; shelve. }
      { (* C  *)
        case b;
        match goal with |- branch_collect_csm ?c ?cs =>
          Tac.elist_add cs c; constructor
        end.
      }
      { (* E *)
        match goal with |- _ = List.fold_left _ ?cs _ =>
          Tac.elist_end cs
        end.
        cbn. reflexivity.
      }
      cbn.
      case b.
      * refine (TrSpec_branch_0 _ _); Tac.build_i_spec_t_eq.
      * Tac.build_Tr_change_exact.
    *)
  - Tac.build_Tr_change_exact.
  *)
  - (* WLP     *)
    cbn.
    FP.simpl_prog.
    FP.by_wlp.
    intuition congruence.
Qed.

Definition cp_a1a: f_impl _ vprog_a1a.
Proof. Tac.extract_impl. Defined.


Inductive bool3 : Set := B0 | B1 | B2.

Definition sig_a1b := mk_f_sig (bool3 * ptr) unit.
Definition spec_a1b : FSpec sig_a1b (fun '(b, p) =>
  Spec.Expanded.mk_r0 (fun n =>
  Spec.Expanded.mk_r1 [] [CTX.mka (SLprop.cell p, n)] (b <> B2) (fun _ =>
  Spec.Expanded.mk_r2 (fun n' =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p, n')] (b <> B1 -> n' = 0))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1b : f_body SPEC sig_a1b := fun '(b, p) =>
  match b with
  | B0 => Write _ p 0
  | B1 | B2 => Ret _ tt (fun _ => [])
  end.
Lemma imatch_a1b:
  f_body_match SPEC vprog_a1b (m_spec spec_a1b).
Proof.
  intros (b, p).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition congruence.
Qed.


Definition sig_a1c := mk_f_sig (option nat * ptr) unit.
Definition spec_a1c : FSpec sig_a1c (fun '(o, p) =>
  Spec.Expanded.mk_r0 (fun n =>
  Spec.Expanded.mk_r1 [] [CTX.mka (SLprop.cell p, n)]
    (n > 0 /\ match o with Some n' => n' > 0 | None => True end) (fun _ =>
  Spec.Expanded.mk_r2 (fun n' =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p, n')] (n' > 0))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1c : f_body SPEC sig_a1c := fun '(o, p) =>
  match o with
  | Some n => Write _ p n
  | None   => Ret _ tt (fun _ => [])
  end.
Lemma imatch_a1c:
  f_body_match SPEC vprog_a1c (m_spec spec_a1c).
Proof.
  intros (o, p).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp_ false.
  destruct o; tauto.
Qed.


Definition sig_a2a := mk_f_sig (ptr * ptr) unit.
Definition spec_a2a : FSpec sig_a2a (fun '(p0, p1) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p0, n0)] [CTX.mka (SLprop.cell p1, n1)]
    (n0 <= n1) (fun _ =>
  Spec.Expanded.mk_r2 (fun n1' =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p1, n1')] (n0 <= n1'))))).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a2a : f_body SPEC sig_a2a := fun '(p0, p1) =>
  Bind _ (Read _ p1) (fun v1 =>
  Bind _ (GGet _ (SLprop.cell p0)) (fun v0 =>
  Bind _ (Assert _ (fun 'tt => ([], v0 <= v1))) (fun _ =>
          Write _ p1 (S v1)))).
Lemma imatch_a2a:
  f_body_match SPEC vprog_a2a (m_spec spec_a2a).
Proof.
  intros (p0, p1).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition.
Qed.
Definition cp_a2a: f_impl _ vprog_a2a.
Proof. Tac.extract_impl. Defined.

Definition vprog_a2b : f_body SPEC sig_a2a := fun '(p0, p1) =>
  Bind _ (Bind _ (Read _ p1) (fun v1 =>
          Bind _ (GGet _ (SLprop.cell p0)) (fun v0 =>
          Ret _ (CP.existG _ v1 v0) (fun _ => [])))) (fun '(CP.existG _ v1 v0) =>
  Bind _ (Assert _ (fun 'tt => ([], v0 <= v1))) (fun _ =>
          Write _ p1 (S v1))).
Lemma imatch_a2b:
  f_body_match SPEC vprog_a2b (m_spec spec_a2a).
Proof.
  intros (p0, p1).
  Tac.build_impl_match.
  FP.simpl_prog.
  FP.by_wlp.
  intuition.
Qed.
Definition cp_a2b: f_impl _ vprog_a2b.
Proof. Tac.extract_impl. Defined.
