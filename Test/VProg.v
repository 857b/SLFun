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
  (*
  refine (intro_impl_match1 _ _ _ _); cbn;
  (* intro and destruct sel0 *)
  intro;
  repeat lazymatch goal with
  |- Impl_Match _ _ (match ?x with _ => _ end) => destruct x
  end.

  simple refine (@Impl_MatchI _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  1,3,5:shelve.
  - (* F0      *) cbn.
    Tac.build_spec.
    (*
    simple refine (Call_SpecI _ _ _ _ _ _ _ _ _).
    1,2,4,6:shelve.
    + (* ij_pre *)
      cbn.
      repeat lazymatch goal with |- CTX.Inj.ieq (Spec.pre ?x) _ _ =>
        Tac.build_matched_shape x; cbn
      end.
      CTX.Inj.build.
    + (* ij_prs *)
      cbn.
      CTX.Inj.build.
    + (* SF *)
      cbn.
      reflexivity.
    *)
  - (* F       *) Tac.cbn_refl.
  - (* EX_SEL1 *) cbn; repeat intro; Tac.simplify_ex_eq_tuple.
  - (* rsel    *) cbn; repeat intro; Tuple.build_shape.
  - (* RSEL    *) cbn; repeat intro; CTX.Inj.build.
  *)
  - (* WLP     *)
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
  (*
  refine (intro_impl_match1 _ _ _ _); cbn;
  (* intro and destruct sel0 *)
  intro;
  repeat lazymatch goal with
  |- Impl_Match _ _ (match ?x with _ => _ end) => destruct x
  end.

  simple refine (@Impl_MatchI _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  1,3,5:shelve.
  - (* F0 *) cbn.
    Tac.build_spec.
    (*
    Tac.build_Bind_init.
    + (* S_F *)
      Tac.build_spec.
      (**)
      hnf.
      match goal with |- (let (a, _) := i_spec (match ?x with _ => _ end) _ in a) ?s =>
        idtac x s;
        simple refine (VProg.Tac.change_arg _ s _ _);
        [ destruct x; [(* only one case *)]; shelve
        | destruct x; cbn; Tac.build_spec
        | simple refine (VProg.Tac.intro_i_spec_t_eq _ _);
          [ shelve | shelve | (* sf_spec *) destruct x; shelve
          | destruct x; cbn;
            refine (conj eq_refl (exist _ eq_refl _));
            cbn; reflexivity ] ]
      end.
      (**)
    + (* F_PRD *) Tac.cbn_refl.
    + (* S_G0  *) cbn; repeat intro; Tac.build_spec.
    + (* S_G   *) Tac.cbn_refl.
    + (* CSM   *) Tac.cbn_refl.
    + (* PRD   *) Tac.cbn_refl.
    + (* SPEC  *) Tac.cbn_refl.
    *)
  - (* F       *) Tac.cbn_refl.
  - (* EX_SEL1 *) cbn; repeat intro; Tac.simplify_ex_eq_tuple.
  - (* rsel *) cbn; repeat intro; Tuple.build_shape.
  - (* RSEL *) cbn; repeat intro; CTX.Inj.build.
  *)
  - (* WLP *)
    cbn.
    FP.by_wlp.
    (*
    refine (FunProg.by_wlp_lem _ _).
    + refine (FP.wlp_formula_Bind _ _). 2:cbn; repeat intro; FP.build_wlp_formula.
      refine (FP.wlp_formula_Bind _ _). 2:cbn; repeat intro; FP.build_wlp_formula.
      FP.build_wlp_formula.
      (*
      simple refine (FP.wlp_formula_imp _ _ _).
      * destruct ps; shelve.
      * destruct ps. FP.build_wlp_formula.
      * intros post f.
        case_eq ps.
        exact f.
      *)
    *)
    + cbn. tauto.
Qed.

Definition cp_a0: f_impl _ vprog_a0.
Proof. Tac.extract_impl. Defined.

