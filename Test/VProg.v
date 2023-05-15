Require Import SLFun.Util SLFun.Values SLFun.SL.
Require Import SLFun.VProg.

Require Import Coq.Lists.List.

Import SLNotations SL.Tactics.
Import ListNotations.
Import DTuple.Notations.
Import VProg._Abbrev.
Import VProg.Notations.

Section Program.
  Variables (SIG : sig_context) (SPEC : CP.spec_context SIG).


Definition spec_0 : FDecl (ptr * ptr) _ unit _
  FOR (p0, p1)
  FOR (n0, n1) [] [vptr p0 ~> n0; vptr p1 ~> n1] True
  RET _ FOR tt [vptr p0 ~> n1; vptr p1 ~> n0] True.
Proof. Derive. Defined.
Variable f_0 : spec_0 _ SPEC.

Definition vprog_0 : FImpl f_0 := fun '(p0, p1) =>
  'v0 <- Read p0;
  'v1 <- Read p1;
  Write p0 v1;;
  Write p1 v0.
Lemma correct_0 : FCorrect vprog_0.
Proof. by_wlp. Qed.
Definition cp_0: f_extract vprog_0.
Proof. Derive. Defined.


Definition spec_1 : FDecl (ptr * ptr * ptr) _ unit _
  FOR (p0, p1, p2)
  FOR (n0, n1, n2) [vptr p2 ~> n2] [vptr p0 ~> n0; vptr p1 ~> n1] True
  RET _ FOR tt [vptr p0 ~> n1; vptr p1 ~> n0] True.
Proof. Derive. Defined.
Variable f_1 : spec_1 _ SPEC.

Definition vprog_1 : FImpl f_1 := fun '(p0, p1, p2) =>
  f_0 (p0, p1).
Lemma correct_1 : FCorrect vprog_1.
Proof. by_wlp. Qed.
Definition cp_1: f_extract vprog_1.
Proof. Derive. Defined.


Definition data42 : nat := 42.

Definition spec_2 : FDecl (ptr * ptr * ptr) _ ptr _
  FOR (p0, p1, p2)
  FOR (n0, n1, n2) [vptr p2 ~> n2] [vptr p0 ~> n0; vptr p1 ~> n1] True
  RET p FOR (n, n1') [vptr p ~> n; vptr p1 ~> n1'] (n1' > 0).
Proof. Derive. Defined.
Variable f_2 : spec_2 _ SPEC.

Definition vprog_2 : FImpl f_2 := fun '(p0, p1, p2) =>
  'v0 <- Read p0;
  Write p1 data42;;
  Assert (fun '(v0', v1') =>
    ([vptr p0 ~> v0'; vptr p1 ~> v1'], v0' = v0));;
  Ret p0 (pt := fun p => [vptr p ~>]).
Lemma correct_2: FCorrect vprog_2.
Proof.
  by_wlp.
  unfold data42; repeat constructor.
Qed.
Definition cp_2: f_extract vprog_2.
Proof. Derive. Defined.


Definition spec_3 : FDecl ptr (Some (fun _ => ptr)) ptr (Some (fun _ => ptr))
  FOR p0 & p1
  FOR (n0, n1) [] [vptr p0 ~> n0; vptr p1 ~> n1] True
  RET p0' & p1' FOR (n0', n1') [vptr p0' ~> n0'; vptr p1' ~> n1'] True.
Proof. Derive. Defined.
Variable f_3 : spec_3 _ SPEC.

Definition vprog_3 : FImpl f_3 := fun p0 p1 =>
  RetG p0 p1 (pt := fun p0 p1 => [vptr p0 ~>; vptr p1 ~>]).
Lemma correct_3: FCorrect vprog_3.
Proof. by_wlp. Qed.
Definition cp_3: f_extract vprog_3.
Proof. Derive. Defined.


Definition spec_4 : FDecl (ptr * ptr) _ ptr (Some (fun _ => ptr))
  FOR (p0, p1)
  FOR (n0, n1) [] [vptr p0 ~> n0; vptr p1 ~> n1] True
  RET p0' & p1' FOR (n0', n1') [vptr p0' ~> n0'; vptr p1' ~> n1'] True.
Proof. Derive. Defined.
Variable f_4 : spec_4 _ SPEC.

Definition vprog_4 : FImpl f_4 := fun '(p0, p1) =>
  'p0' p1' <- f_3 p0 p1;
  RetG p0' p1' (pt := fun p0 p1 => [vptr p0 ~>; vptr p1 ~>]).
Lemma correct_4: FCorrect vprog_4.
Proof. by_wlp. Qed.
Definition cp_4: f_extract vprog_4.
Proof. Derive. Defined.


Definition cell2 (p : ptr) '(v0, v1) : SLprop.t :=
  (SLprop.cell p v0 ** SLprop.cell (S p) v1)%slprop.

Definition elim_cell2_spec : LDecl ptr unit
  FOR p FOR n01 [] [cell2 p ~> n01] True
  RET _ FOR tt [vptr p ~> (fst n01); vptr (S p) ~> (snd n01)] True.
Proof. Derive. Defined.
Lemma elim_cell2 : elim_cell2_spec.
Proof.
  init_lemma p (n0, n1) _.
  reflexivity.
Qed.

Definition intro_cell2_spec : LDecl ptr unit
  FOR p FOR (n0, n1) [] [vptr p ~> n0; vptr (S p) ~> n1] True
  RET _ FOR tt [cell2 p ~> (n0, n1)] True.
Proof. Derive. Defined.
Lemma intro_cell2 : intro_cell2_spec.
Proof.
  init_lemma p (n0, n1) _.
  reflexivity.
Qed.

(*
Global Opaque cell2.
Global Arguments cell2 : simpl never.
*)

Definition spec_5 : FDecl ptr _ unit _
  FOR p
  FOR v [] [cell2 p ~> v] True
  RET _ FOR v' [cell2 p ~> v'] (v' = let (n0, n1) := v in (S n0, n1)).
Proof. Derive. Defined.
Variable f_5 : spec_5 _ SPEC.

Definition vprog_5 : FImpl f_5 := fun p =>
  gLem elim_cell2 p;;
  'n <- Read p;
  Write p (S n);;
  gLem intro_cell2 p.
Lemma correct_5: FCorrect vprog_5.
Proof. by_wlp. case sel0; reflexivity. Qed.
Definition cp_5: f_extract vprog_5.
Proof. Derive. Defined.

End Program.

Section Extraction.
  Definition SIG : sig_context :=
    fun f => match f with
    | 0 => Some (fd_sig spec_0)
    | 1 => Some (fd_sig spec_1)
    | 2 => Some (fd_sig spec_2)
    | 3 => Some (fd_sig spec_3)
    | 4 => Some (fd_sig spec_4)
    | 5 => Some (fd_sig spec_5)
    | _ => None
    end.

  Definition SPEC : CP.spec_context SIG :=
    fun f => match f with
    | 0 => fd_cp spec_0
    | 1 => fd_cp spec_1
    | 2 => fd_cp spec_2
    | 3 => fd_cp spec_3
    | 4 => fd_cp spec_4
    | 5 => fd_cp spec_5
    | _ => tt
    end.

  Definition H_f_0 := fd_mk 0 spec_0 SPEC eq_refl eq_refl.
  Definition H_f_1 := fd_mk 1 spec_1 SPEC eq_refl eq_refl.
  Definition H_f_2 := fd_mk 2 spec_2 SPEC eq_refl eq_refl.
  Definition H_f_3 := fd_mk 3 spec_3 SPEC eq_refl eq_refl.
  Definition H_f_4 := fd_mk 4 spec_4 SPEC eq_refl eq_refl.
  Definition H_f_5 := fd_mk 5 spec_5 SPEC eq_refl eq_refl.

  Definition IMPL : CP.impl_context SIG :=
    fun f => match f with
    | 0 => proj1_sig (cp_0 _ _ H_f_0)
    | 1 => proj1_sig (cp_1 _ _ H_f_0 H_f_1)
    | 2 => proj1_sig (cp_2 _ _ H_f_2)
    | 3 => proj1_sig (cp_3 _ _ H_f_3)
    | 4 => proj1_sig (cp_4 _ _ H_f_3 H_f_4)
    | 5 => proj1_sig (cp_5 _ _ H_f_5)
    | _ => tt
    end.

  Lemma match_context:
    CP.context_match_spec IMPL SPEC.
  Proof.
    Tac.case_until_True;
    cbn beta iota delta [SIG IMPL SPEC];
    apply f_extract_match_spec.
    - apply correct_0.
    - apply correct_1.
    - apply correct_2.
    - apply correct_3.
    - apply correct_4.
    - apply correct_5.
  Qed.

  Lemma context_oracle_free:
    CP.context_oracle_free IMPL.
  Proof.
    Tac.case_until_True;
    cbn beta iota delta [SIG IMPL SPEC];
    apply f_extract_oracle_free.
  Qed.
End Extraction.

Section Other.

Definition sigh_a0 := mk_f_sig1 (ptr * ptr) None unit None.
Definition spec_a0 : FSpec sigh_a0
  FOR ps
  FOR n [vptr (fst ps) ~> n] [] True
  RET _ FOR tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0 : f_body SPEC sigh_a0 := fun ps =>
  'v0 <- let (p0, _) := ps in Read p0;
  Ret tt.
Lemma imatch_a0:
  f_body_match vprog_a0 (m_spec spec_a0).
Proof. by_wlp. Qed.

Definition cp_a0: f_extract vprog_a0.
Proof. Tac.extract_impl. Defined.


Definition sigh_a1a := mk_f_sig1 (bool * ptr * ptr * ptr) None unit None.
Definition spec_a1a : FSpec sigh_a1a
  FOR (b, p0, p1, p2)
  FOR (n0, n1, n2) [vptr p0 ~> n0] [vptr p1 ~> n1; vptr p2 ~> n2] True
  RET _ FOR (n1', n2') [vptr p1 ~> n1'; vptr p2 ~> n2'] (b = true -> n1' = 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1a : f_body SPEC sigh_a1a := fun '(b, p0, p1, p2) =>
  if b
  then Write p1 0
  else Write p2 1.
Lemma imatch_a1a:
  f_body_match vprog_a1a (m_spec spec_a1a).
Proof. by_wlp; congruence. Qed.

Definition cp_a1a: f_extract vprog_a1a.
Proof. Tac.extract_impl. Defined.


Inductive bool3 : Set := B0 | B1 | B2.

Definition sigh_a1b := mk_f_sig1 (bool3 * ptr) None unit None.
Definition spec_a1b : FSpec sigh_a1b
  FOR (b, p)
  FOR n [] [vptr p ~> n] (b <> B2)
  RET _ FOR n' [vptr p ~> n'] (b <> B1 -> n' = 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1b : f_body SPEC sigh_a1b := fun '(b, p) =>
  match b with
  | B0 => Write p 0
  | B1 | B2 => Ret tt
  end.
Lemma imatch_a1b:
  f_body_match vprog_a1b (m_spec spec_a1b).
Proof. by_wlp; congruence. Qed.


Definition sigh_a1c := mk_f_sig1 (option nat * ptr) None unit None.
Definition spec_a1c : FSpec sigh_a1c
  FOR (o, p)
  FOR n [] [vptr p ~> n] (n > 0 /\ match o with Some n' => n' > 0 | None => True end)
  RET _ FOR n' [vptr p ~> n'] (n' > 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1c : f_body SPEC sigh_a1c := fun '(o, p) =>
  match o with
  | Some n => Write p n
  | None   => Ret tt
  end.
Lemma imatch_a1c:
  f_body_match vprog_a1c (m_spec spec_a1c).
Proof. by_wlp. Qed.


Definition sigh_a2a := mk_f_sig1 (ptr * ptr) None unit None.
Definition spec_a2a : FSpec sigh_a2a
  FOR (p0, p1)
  FOR (n0, n1) [vptr p0 ~> n0] [vptr p1 ~> n1] (n0 <= n1)
  RET _ FOR n1' [vptr p1 ~> n1'] (n0 <= n1').
Proof. Tac.build_FSpec. Defined.

Definition vprog_a2a : f_body SPEC sigh_a2a := fun '(p0, p1) =>
  'v1 <- Read p1;
  'v0 <- gGet (SLprop.cell p0);
  Assert (fun 'tt => ([], v0 <= v1));;
  Write p1 (S v1).
Lemma imatch_a2a:
  f_body_match vprog_a2a (m_spec spec_a2a).
Proof. by_wlp. Qed.
Definition cp_a2a: f_extract vprog_a2a.
Proof. Tac.extract_impl. Defined.

Definition vprog_a2b : f_body SPEC sigh_a2a := fun '(p0, p1) =>
  'v1 v0 <- (
    'v1 <- Read p1;
    'v0 <- gGet (SLprop.cell p0);
    RetG v1 v0);
  Assert (fun 'tt => ([], v0 <= v1));;
  Write p1 (S v1).
Lemma imatch_a2b:
  f_body_match vprog_a2b (m_spec spec_a2a).
Proof. by_wlp. Qed.
Definition cp_a2b: f_extract vprog_a2b.
Proof. Tac.extract_impl. Defined.


Definition sigh_a3 := mk_f_sig1 unit (Some (fun _ => (nat * nat)%type <: Type)) unit (Some (fun _ => nat <: Type)).
Definition spec_a3 : FSpec sigh_a3
  FOR _ & (n0, n1)
  FOR tt [] [] True
  RET _ & r FOR tt [] (r = n0 + n1).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a3 : f_body SPEC sigh_a3 := fun _ '(n0, n1) =>
  RetG tt (n0 + n1).
Lemma imatch_a3:
  f_body_match vprog_a3 (m_spec spec_a3).
Proof. by_wlp. Qed.
Definition cp_a3: f_extract vprog_a3.
Proof. Tac.extract_impl. Defined.
End Other.
