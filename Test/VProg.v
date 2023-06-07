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
Proof.
  solve_by_wlp;
  case sel0; reflexivity.
Qed.

Definition spec_6 : FDecl SPEC
  (p : ptr) 'v [cell2 p ~> v] [] True
  '(n : nat) tt [] (n = fst v).
Proof. Derived. Defined.
Variable f_6 : spec_6 CT.

Definition vprog_6 : FImpl f_6 := fun p =>
  'v <- vfrag_0 p;
  Ret (fst v).
Lemma correct_6: FCorrect vprog_6.
Proof. solve_by_wlp. Qed.


Definition spec_7 : FDecl SPEC
  ((p0, p1, p2) : ptr * ptr * ptr) '(v0, v1, v2) [vptr p2 ~> v2] [vptr p0 ~> v0; vptr p1 ~> v1]
    (v0 >= 1 /\ v1 >= 1 /\ v2 >= 1)
  '(p : ptr) (v', v1') [vptr p ~> v'; vptr p1 ~> v1'] (v1 >= 1).
Proof. Derived. Defined.
Variable f_7 : spec_7 CT.

Definition vprog_7 : FImpl f_7 := fun '(p0, p1, p2) =>
  Loop0 (fun p => [vptr (sumv p)~>]) None (inl p0) (fun p =>
    'v <- Read p;
    match v with
    | O   => Ret (inr p) (pt := fun p => [vptr (sumv p)~>])
    | S n =>
        Write p n;;
        'v2 <- Read p2;
        Write p1 v2;;
        Ret (inl p) (pt := fun p => [vptr (sumv p)~>])
    end
  ).
Lemma correct_7 : FCorrect vprog_7.
Proof.
  solve_by_wlp.
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

Section Other.
  Variable CT : ConcreteProg.context.

Definition vdummy (A : Type) : Vprop.p A :=
  fun _ => SLprop.emp.
Definition remove_vdummy_spec : LDecl SPEC
  (A : Type) 'v [] [vdummy A ~> v] True
  '(_ : unit) tt [] True.
Proof. Derived. Defined.
Lemma remove_vdummy : remove_vdummy_spec.
Proof.
  init_lemma n v ?.
  reflexivity.
Qed.


Definition sigh_a0a := mk_f_sig1 (ptr * ptr) None unit None.
Definition spec_a0a : FSpec sigh_a0a
  SPEC (ps : _) 'n [vptr (fst ps) ~> n] [] True
  '(_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0a : f_body CT sigh_a0a := fun ps =>
  'v0 <- let (p0, _) := ps in Read p0;
  Ret tt.
Lemma imatch_a0a:
  f_body_match vprog_a0a (m_spec spec_a0a).
Proof. solve_by_wlp. Qed.

Definition cp_a0a: f_extract vprog_a0a.
Proof. Tac.extract_impl. Defined.

Definition sigh_a0b := mk_f_sig1 (ptr * ptr) None memdata None.
Definition spec_a0b : FSpec sigh_a0b
  SPEC (ps : _) 'n [vptr (fst ps) ~> n] [] True
  '(_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0b : f_body CT sigh_a0b := fun ps =>
  let (p0, _) := ps in
  Read p0.

Lemma imatch_a0b:
  f_body_match vprog_a0b (m_spec spec_a0b).
Proof. solve_by_wlp. Qed.

Definition cp_a0b: f_extract vprog_a0b.
Proof. Tac.extract_impl. Defined.


Definition sigh_a0c := mk_f_sig1 (nat * nat) None unit None.
Definition spec_a0c : FSpec sigh_a0c
  SPEC (ns : _) '(v0, v1) [] [vdummy (Fin.t (fst ns)) ~> v0; vdummy (Fin.t (snd ns)) ~> v1] True
  '(_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0c : f_body CT sigh_a0c := fun ns =>
  let (n0, n1) := ns in
  gLem remove_vdummy (Fin.t n0);;
  gLem remove_vdummy (Fin.t n1).

Lemma imatch_a0c:
  f_body_match vprog_a0c (m_spec spec_a0c).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Definition cp_a0c: f_extract vprog_a0c.
Proof. Tac.extract_impl. Defined.


Definition sigh_a0d := mk_f_sig1 (nat * nat) (Some (fun x => Fin.t (fst x) <: Type))
                                 nat (Some (fun x => Fin.t x <: Type)).
Definition spec_a0d : FSpec sigh_a0d
  SPEC (ns : _) & (_ : _) 'v [] [vdummy (Fin.t (snd ns)) ~> v] True
  '(_ : _) & (_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0d : f_body CT sigh_a0d := fun ns g =>
  (let (n0, n1) as ns return Fin.t (fst ns) -> _ := ns in fun g =>
   gLem remove_vdummy (Fin.t n1);;
   RetG n0 g) g.

Lemma imatch_a0d:
  f_body_match vprog_a0d (m_spec spec_a0d).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Definition cp_a0d: f_extract vprog_a0d.
Proof. Tac.extract_impl. Defined.


Definition sigh_a0e := mk_f_sig1 (nat * nat) (Some (fun x => (Fin.t (fst x) * Fin.t (snd x))%type <: Type))
                                 nat None.
Definition spec_a0e : FSpec sigh_a0e
  SPEC (ns : _) & (_ : _) 'tt [] [] True
  '(_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0e : f_body CT sigh_a0e := fun ns gs =>
  let (g0, g1) := gs in
  (let (n0, n1) as ns return Fin.t (fst ns) -> Fin.t (snd ns) -> _ := ns in fun g0 g1 =>
   Ret n0) g0 g1.

Goal f_body_match vprog_a0e (m_spec spec_a0e).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.
Goal f_extract vprog_a0e.
Proof. Tac.extract_impl. Defined.


Definition sigh_a1a := mk_f_sig1 (bool * ptr * ptr * ptr) None unit None.
Definition spec_a1a : FSpec sigh_a1a
  SPEC ((b, p0, p1, p2) : _)
  '(n0, n1, n2) [vptr p0 ~> n0] [vptr p1 ~> n1; vptr p2 ~> n2] True
  '(_ : _) (n1', n2') [vptr p1 ~> n1'; vptr p2 ~> n2'] (b = true -> n1' = 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1a : f_body CT sigh_a1a := fun '(b, p0, p1, p2) =>
  if b
  then Write p1 0
  else Write p2 1.
Goal f_body_match vprog_a1a (m_spec spec_a1a).
Proof. solve_by_wlp; congruence. Qed.
Goal f_extract vprog_a1a.
Proof. Tac.extract_impl. Defined.


Inductive bool3 : Set := B0 | B1 | B2.

Definition sigh_a1b := mk_f_sig1 (bool3 * ptr) None unit None.
Definition spec_a1b : FSpec sigh_a1b
  SPEC ((b, p) : _)
  'n [] [vptr p ~> n] (b <> B2)
  '(_ : _) n' [vptr p ~> n'] (b <> B1 -> n' = 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1b : f_body CT sigh_a1b := fun '(b, p) =>
  match b with
  | B0 => Write p 0
  | B1 | B2 => Ret tt
  end.
Goal f_body_match vprog_a1b (m_spec spec_a1b).
Proof. solve_by_wlp; congruence. Qed.
Goal f_extract vprog_a1b.
Proof. Tac.extract_impl. Defined.


Definition sigh_a1c := mk_f_sig1 (option nat * ptr) None unit None.
Definition spec_a1c : FSpec sigh_a1c
  SPEC ((o, p) : _)
  'n [] [vptr p ~> n] (n > 0 /\ match o with Some n' => n' > 0 | None => True end)
  '(_ : _) n' [vptr p ~> n'] (n' > 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1c : f_body CT sigh_a1c := fun '(o, p) =>
  match o with
  | Some n => Write p n
  | None   => Ret tt
  end.
Goal f_body_match vprog_a1c (m_spec spec_a1c).
Proof. solve_by_wlp. Qed.
Goal f_extract vprog_a1c.
Proof. Tac.extract_impl. Defined.


Definition sigh_a1d := mk_f_sig1 bool None unit None.
Definition spec_a1d : FSpec sigh_a1d
  SPEC (b : bool)
  'v [] [(if b as b return Vprop.p (if b then nat else bool) then vdummy nat else vdummy bool) ~> v] True
  '(_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1d : f_body CT sigh_a1d := fun b =>
  if b
  then gLem remove_vdummy nat
  else gLem remove_vdummy bool.
Goal f_body_match vprog_a1d (m_spec spec_a1d).
Proof. solve_by_wlp. Qed.
Goal f_extract vprog_a1d.
Proof. Tac.extract_impl. Defined.


Definition sigh_a1e := mk_f_sig1 bool (Some (fun b : bool => (if b then nat else unit) <: Type))
                                 unit (Some (fun _ => option nat <: Type)).
Definition spec_a1e : FSpec sigh_a1e
  SPEC (b : bool) & (_ : _)
  'tt [] [] True
  '(_ : _) & (_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1e : f_body CT sigh_a1e := fun b g =>
  (if b as b return (if b then nat else unit) -> _
   then fun g => RetG tt (Some g)
   else fun _ => RetG tt None
  ) g.
Goal f_body_match vprog_a1e (m_spec spec_a1e).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.
Goal f_extract vprog_a1e.
Proof. Tac.extract_impl. Defined.


Definition sigh_a2a := mk_f_sig1 (ptr * ptr) None unit None.
Definition spec_a2a : FSpec sigh_a2a
  SPEC ((p0, p1) : _)
  '(n0, n1) [vptr p0 ~> n0] [vptr p1 ~> n1] (n0 <= n1)
  '(_ : _) n1' [vptr p1 ~> n1'] (n0 <= n1').
Proof. Tac.build_FSpec. Defined.

Definition vprog_a2a : f_body CT sigh_a2a := fun '(p0, p1) =>
  'v1 <- Read p1;
  'v0 <- gGet (SLprop.cell p0);
  Assert (fun 'tt => ([], v0 <= v1));;
  Write p1 (S v1).
Lemma imatch_a2a:
  f_body_match vprog_a2a (m_spec spec_a2a).
Proof. solve_by_wlp. Qed.
Definition cp_a2a: f_extract vprog_a2a.
Proof. Tac.extract_impl. Defined.

Definition vprog_a2b : f_body CT sigh_a2a := fun '(p0, p1) =>
  'v1 v0 <- (
    'v1 <- Read p1;
    'v0 <- gGet (SLprop.cell p0);
    RetG v1 v0);
  Assert (fun 'tt => ([], v0 <= v1));;
  Write p1 (S v1).
Lemma imatch_a2b:
  f_body_match vprog_a2b (m_spec spec_a2a).
Proof. solve_by_wlp. Qed.
Definition cp_a2b: f_extract vprog_a2b.
Proof. Tac.extract_impl. Defined.


Definition sigh_a3a := mk_f_sig1 unit (Some (fun _ => (nat * nat)%type <: Type)) unit (Some (fun _ => nat <: Type)).
Definition spec_a3a : FSpec sigh_a3a
  SPEC (_ : _) & ((n0, n1) : _)
  'tt [] [] True
  '(_ : _) & (r : _) tt [] (r = n0 + n1).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a3a : f_body CT sigh_a3a := fun _ '(n0, n1) =>
  RetG tt (n0 + n1).
Lemma imatch_a3a:
  f_body_match vprog_a3a (m_spec spec_a3a).
Proof. solve_by_wlp. Qed.
Definition cp_a3a: f_extract vprog_a3a.
Proof. Tac.extract_impl. Defined.


Definition sigh_a3b := mk_f_sig1 (nat * unit) (Some (fun '(_,_) => nat <: Type)) nat None.
Definition spec_a3b : FSpec sigh_a3b
  SPEC ((_, _) : _) & (_ : _)
  'tt [] [] True
  '(_ : _) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a3b : f_body CT sigh_a3b := fun '(n, _) _ =>
  Ret n.
Lemma imatch_a3b:
  f_body_match vprog_a3b (m_spec spec_a3b).
Proof. solve_by_wlp. Qed.

Definition cp_a3b: f_extract vprog_a3b.
Proof. Tac.extract_impl. Defined.

End Other.
