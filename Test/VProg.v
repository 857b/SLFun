Require Import SLFun.Util SLFun.Values SLFun.SL.
Require Import SLFun.VProg.

Require Import Coq.Lists.List.

Import SLNotations.
Import ListNotations.
Import VProg._Abbrev.


Definition f_main : fid := 0.

Definition sig_main := mk_f_sig (ptr * ptr * ptr) ptr.

Definition SIG : sig_context :=
  fun f => match f with
  | 0 => Some sig_main
  | _ => None
  end.

Definition spec_main : FSpec sig_main (fun '(p0, p1, p2) =>
  Spec.Expanded.mk_r0 (fun '(n0, n1, n2) =>
  Spec.Expanded.mk_r1 [CTX.mka (SLprop.cell p2, n2)]
             [CTX.mka (SLprop.cell p0, n0); CTX.mka (SLprop.cell p1, n1)] True (fun p =>
  Spec.Expanded.mk_r2 (fun '(n, n1') =>
  Spec.Expanded.mk_r3 [CTX.mka (SLprop.cell p, n); CTX.mka (SLprop.cell p1, n1')] (n1' > 0))))).
Proof.
  Tac.build_FSpec.
  (*
  refine (VProg.Tac.mk_red_FSpec _ _); cbn.
  intro ax. Tac.of_expanded_arg.
  refine (Spec.Expanded.of_expandedI _ _ _); cbn.
  intro sel0. Tac.of_expanded_arg.
  refine (Spec.Expanded.of_expanded1I _ _ _); cbn.
  intro rx.
  simple refine (Spec.Expanded.of_expanded2I _ _ _ _ _ _).
  1,2,3,4,6,8:shelve.
  { (* sel1_TU_GOAL *) cbn; intro (* sel1 *); Tuple.build_type_iso_tu. }
  { (* S_VPOST *) Tac.cbn_refl. }
  { (* S3 *) cbn; repeat intro; refine (Spec.Expanded.of_expanded3I _). }
  cbn. reflexivity.
  *)
Defined.


Definition SPEC : CP.spec_context SIG :=
  fun f => match f with
  | 0 => SP.tr_f_spec (tr_f_spec (m_spec spec_main))
  | _ => tt
  end.

Definition data42 : nat := 42.

Definition vprog_main (ps : ptr * ptr * ptr) : instr SPEC ptr :=
  let '(p0, p1, p2) := ps in
  Bind _ (Read  _ p0) (fun v0 =>
  Bind _ (Write _ p1 data42) (fun _ =>
  Bind _ (Assert _ (fun '(v0', v1') =>
    ([CTX.mka (SLprop.cell p0, v0'); CTX.mka (SLprop.cell p1, v1')], v0' = v0))) (fun _ =>
  Ret _ p0 (fun p => [Vprop.mk (SLprop.cell p)])))).

Definition impl_main (ps : ptr * ptr * ptr) :
  { i : CP.instr ptr | i = i_impl (vprog_main ps) }.
Proof.
  unfold i_impl, vprog_main; cbn.
  case ps as ((p0, p1), p2); cbn.
  eexists. reflexivity.
Defined.

Lemma imatch_main (ps : ptr * ptr * ptr):
  impl_match SPEC (vprog_main ps) (m_spec spec_main ps).
Proof.
  case ps as ((p0, p1), p2).
  Tac.build_impl_match.
  (*
  apply intro_impl_match1.
  cbn.
  intros ((n0, n1), n2).
  (* apply Impl_MatchI. (* Coq 8.15.2 BUG: Anomaly "in retyping: unbound local variable." *) *)
  simple refine (@Impl_MatchI _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  1,3,5:shelve.
  - (* F0      *) cbn. Tac.build_spec.
  - (* F       *) Tac.cbn_refl.
  - (* EX_SEL1 *)
    cbn; repeat intro.
    Tac.simplify_ex_eq_tuple.
    (*
    etransitivity.
    + etransitivity.
      refine (exists_eq_const _ _ (fun x => _)).
        refine (ex_ind (fun x => _)).
        refine (VProg.Tac.elim_tuple_eq_conj _).
        cbn; repeat intro; eassumption.
      refine (exists_eq_const _ _ (fun x => _)).
        refine (VProg.Tac.elim_tuple_eq_conj _).
        cbn; repeat intro; eassumption.
    + refine (VProg.Tac.simpl_tuple_eq_conj _ _).
      * cbn.
        refine (simpl_and_list_r1 eq_refl _).
        refine (simpl_and_list_r1 eq_refl _).
        refine (simpl_and_list_e1 _).
        exact simpl_and_list_0.
      * cbn; reflexivity.
    *)
  - (* rsel    *) cbn; repeat intro. Tuple.build_shape.
  - (* RSEL    *) cbn; repeat intro. CTX.Inj.build.
  *)
  - (* WLP *)
    cbn.
    unfold FP.BindA; cbn.
    intuition.
    unfold data42; repeat constructor.
Qed.
