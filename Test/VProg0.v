From SLFun Require Import Util Values SL VProg.Main.
From Coq   Require Import Lists.List.

Import SLNotations ListNotations FunProg.Notations VProg.Core.Abbrev VProg.Main.Notations.
Import SL.Tactics.

Section Program.
  Variable (CT : CP.context).


Definition spec_0 : FDecl SPEC
  ((p0, p1) : ptr * ptr)
  '(n0, n1) [] [vptr p0 ~> n0; vptr p1 ~> n1] True
  '(_ : unit) tt [vptr p0 ~> n1; vptr p1 ~> n0] True.
Proof. Derived. Defined.
Variable f_0 : spec_0 CT.

Definition vprog_0 : FImpl f_0 := fun '(p0, p1) =>
  'v0 <- Read p0;
  'v1 <- Read p1;
  Write p0 v1;;
  Write p1 v0.
Lemma correct_0 : FCorrect vprog_0.
Proof. solve_by_wlp. Qed.


Definition spec_1 : FDecl SPEC
  ((p0, p1, p2) : ptr * ptr * ptr)
  '(n0, n1, n2) [vptr p2 ~> n2] [vptr p0 ~> n0; vptr p1 ~> n1] True
  '(_ : unit) tt [vptr p0 ~> n1; vptr p1 ~> n0] True.
Proof. Derived. Defined.
Variable f_1 : spec_1 CT.

Definition vprog_1 : FImpl f_1 := fun '(p0, p1, p2) =>
  f_0 (p0, p1).
Lemma correct_1 : FCorrect vprog_1.
Proof. solve_by_wlp. Qed.


Definition data42 : nat := 42.

Definition spec_2 : FDecl SPEC
  ((p0, p1, p2) : ptr * ptr * ptr)
  '(n0, n1, n2) [vptr p2 ~> n2] [vptr p0 ~> n0; vptr p1 ~> n1] True
  '(p : ptr) (n, n1') [vptr p ~> n; vptr p1 ~> n1'] (n1' > 0).
Proof. Derived. Defined.
Variable f_2 : spec_2 CT.

Definition vprog_2 : FImpl f_2 := fun '(p0, p1, p2) =>
  'v0 <- Read p0;
  Write p1 data42;;
  Assert (fun '(v0', v1') =>
    ([vptr p0 ~> v0'; vptr p1 ~> v1'], v0' = v0));;
  Ret p0 (pt := fun p => [vptr p ~>]).
Lemma correct_2: FCorrect vprog_2.
Proof.
  solve_by_wlp.
  unfold data42; repeat constructor.
Qed.


Definition spec_3 : FDecl SPEC
  (p0 : ptr) & (p1 : ptr)
  '(n0, n1) [] [vptr p0 ~> n0; vptr p1 ~> n1] True
  '(p0' : ptr) & (p1' : ptr) (n0', n1') [vptr p0' ~> n0'; vptr p1' ~> n1'] True.
Proof. Derived. Defined.
Variable f_3 : spec_3 CT.

Definition vprog_3 : FImpl f_3 := fun p0 p1 =>
  RetG p0 p1 (pt := fun p0 p1 => [vptr p0 ~>; vptr p1 ~>]).
Lemma correct_3: FCorrect vprog_3.
Proof. solve_by_wlp. Qed.


Definition spec_4 : FDecl SPEC
  ((p0, p1) : ptr * ptr)
  '(n0, n1) [] [vptr p0 ~> n0; vptr p1 ~> n1] True
  '(p0' : ptr) & (p1' : ptr) (n0', n1') [vptr p0' ~> n0'; vptr p1' ~> n1'] True.
Proof. Derived. Defined.
Variable f_4 : spec_4 CT.

Definition vprog_4 : FImpl f_4 := fun '(p0, p1) =>
  'p0' p1' <- f_3 p0 p1;
  RetG p0' p1' (pt := fun p0 p1 => [vptr p0 ~>; vptr p1 ~>]).
Lemma correct_4: FCorrect vprog_4.
Proof. solve_by_wlp. Qed.


Definition cell2 (p : ptr) '(v0, v1) : SLprop.t :=
  (SLprop.cell p v0 ** SLprop.cell (S p) v1)%slprop.

Definition elim_cell2_spec : LDecl SPEC
  (p : ptr) 'n01 [] [cell2 p ~> n01] True
  '(_ : unit) tt [vptr p ~> (fst n01); vptr (S p) ~> (snd n01)] True.
Proof. Derived. Defined.
Lemma elim_cell2 : elim_cell2_spec.
Proof.
  init_lemma p (n0, n1) ?.
  reflexivity.
Qed.

Definition intro_cell2_spec : LDecl SPEC
  (p : ptr) '(n0, n1) [] [vptr p ~> n0; vptr (S p) ~> n1] True
  '(_ : unit) tt [cell2 p ~> (n0, n1)] True.
Proof. Derived. Defined.
Lemma intro_cell2 : intro_cell2_spec.
Proof.
  init_lemma p (n0, n1) ?.
  reflexivity.
Qed.

Definition spec_5 : FDecl SPEC
  (p : ptr) 'v [] [cell2 p ~> v] True
  '(_ : unit) v' [cell2 p ~> v'] (v' = let (n0, n1) := v in (S n0, n1)).
Proof. Derived. Defined.
Variable f_5 : spec_5 CT.

Definition vprog_5 : FImpl f_5 := fun p =>
  gLem elim_cell2 p;;
  'n <- Read p;
  Write p (S n);;
  gLem intro_cell2 p.
Lemma correct_5: FCorrect vprog_5.
Proof. solve_by_wlp. Qed.


Definition spec_f0 : FDecl SPEC
  (p : ptr) 'v [cell2 p ~> v] [] True
  '(r : nat * nat) tt [] (r = v).
Proof. Derived. Defined.

Definition vfrag_0_impl : FragImpl spec_f0 CT :=
  fun p =>
  gLem elim_cell2 p;;
  'n0 <- Read p;
  'n1 <- Read (S p);
  gLem intro_cell2 p;;
  Ret (n0, n1).
Lemma vfrag_0 : FragCorrect vfrag_0_impl.
Proof. solve_by_wlp. Qed.

Definition spec_6 : FDecl SPEC
  (p : ptr) 'v [cell2 p ~> v] [] True
  '(n : nat) tt [] (n = fst v).
Proof. Derived. Defined.
Variable f_6 : spec_6 CT.

Definition vprog_6 : FImpl f_6 := fun p =>
  'v <- vfrag_0 p;
  Ret (fst v).
Lemma correct_6: FCorrect vprog_6.
Proof. solve_by_wlp; congruence. Qed.


Definition spec_7 : FDecl SPEC
  ((p0, p1, p2) : ptr * ptr * ptr) '(v0, v1, v2) [vptr p2 ~> v2] [vptr p0 ~> v0; vptr p1 ~> v1]
    (v0 >= 1 /\ v1 >= 1 /\ v2 >= 1)
  '(p : ptr) (v', v1') [vptr p ~> v'; vptr p1 ~> v1'] (v1 >= 1).
Proof. Derived. Defined.
Variable f_7 : spec_7 CT.

Definition vprog_7 : FImpl f_7 := fun '(p0, p1, p2) =>
  let inv p := [vptr (sumv p)~>] in
  Loop0 inv None (inl p0) (fun p =>
    'v <- Read p;
    match v with
    | O   => Ret (inr p) (pt := inv)
    | S n =>
        Write p n;;
        'v2 <- Read p2;
        Write p1 v2;;
        Ret (inl p) (pt := inv)
    end
  ).
Lemma correct_7 : FCorrect vprog_7.
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
  exists (fun _ _ v1 => v1 >= 1).
  FP.solve_wlp; auto.
Qed.
End Program.

Derive prog SuchThat (CP.of_entries [
  f_entry spec_0 correct_0;
  f_entry spec_1 correct_1;
  f_entry spec_2 correct_2;
  f_entry spec_3 correct_3;
  f_entry spec_4 correct_4;
  f_entry spec_5 correct_5;
  f_entry spec_6 correct_6;
  f_entry spec_7 correct_7
] prog) As prog_correct.
Proof. Derived. Qed.

Definition IMPL : CP.impl_context _ := CP.impl_of_list prog.

Lemma f_0_okstate m p0 p1 s'
  (NN_P0  : p0 <> NULL) (NN_P1  : p1 <> NULL)
  (NALIAS : p0 <> p1)
  (STEPS  : CP.steps IMPL (m, CP.get_fun_body IMPL 0 eq_refl (p0, p1)) s'):
  CP.okstate IMPL s'.
Proof.
  eapply CP.func_okstate in STEPS; eauto.
  1,2:apply prog_correct.
  { cbn.
    eexists _, SLprop.True.
    split. 2:reflexivity.
    unfold tr_f_spec, Spec.tr, Spec.Expanded.tr; cbn.
    exists tt, (m p0, m p1); cbn.
    unshelve eexists. split. reflexivity. }
  cbn.
  eexists (SLProg.fmem_of_mem m); split. apply SLProg.match_fmem_of_mem.
  SL.normalize.
  rewrite <- SLprop.star_assoc.
  ecase FMem.build_join as [fm0 FM0]; cycle 1.
  eexists fm0, (fun p => if Mem.ptr_eq p p0 then None else if Mem.ptr_eq p p1 then None else Some (m p));
    intuition; cycle 1.
  - cbn; eexists _, _; intuition; try reflexivity.
    exact FM0.
  - constructor.
  - intro p; generalize (FM0 p); unfold FMem.cell.
    do 2 case Mem.ptr_eq as [|]; simpl; subst;
    simplify_eq 1; intros <-; reflexivity.
  - intro p; unfold FMem.cell; simpl.
    do 2 case Mem.ptr_eq as [|]; simpl; congruence.
Qed.
