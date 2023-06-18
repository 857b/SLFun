From SLFun Require Import Util Values SL VProg.Main.
From Coq   Require Import Lists.List.

Import SLNotations ListNotations FunProg.Notations VProg.Core.Abbrev VProg.Main.Notations.
Import SL.Tactics.

Section Test.
  Variable CT : ConcreteProg.context.

Definition vdummy (A : Type) : Vprop.p A :=
  fun _ => SLprop.emp.
Derive remove_vdummy_spec SuchThat (
  VLem SPEC (A : Type)
  'v [] [vdummy A ~> v] True
  '(_ : unit) tt [] True
  remove_vdummy_spec) As remove_vdummy.
Proof.
  init_lemma n v ?.
  reflexivity.
Qed.

Definition m_body [sg sgh e] (F : @FSpec sg sgh e) : Type := f_body CT sgh.

Inductive Test [sg sgh] (e : @f_spec_exp sg sgh) (b : f_body CT sgh) : Prop :=
  mk_test_fun
    (S : FSpec sgh e)
    (E : f_erase b)
    (M : f_body_match b (m_spec S)).
Arguments Test _ _ e%vprog_spec.

Ltac init_Test :=
  unshelve eexists; [ Tac.build_FSpec | Tac.erase_impl | cbn ].


Definition test_Ret :
  Test SPEC (p : ptr)
  'n [vptr p ~> n] [] True
  '(r : nat) tt [] True
(fun _ =>
  Ret 42).
Proof.
  init_Test.
  solve_by_wlp.
Qed.

Definition test_dlet :
  Test SPEC ((ps, p1) : (ptr * ptr) * ptr)
  '(n0, n1) [vptr (fst ps) ~> n0] [vptr p1 ~> n1] True
  '(_ : unit) tt [vptr p1 ~> O] True
(fun '(ps, p1) =>
  let '(p0, _) := ps in
  Write p1 O).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.


(* destructive let *)

Definition spec_a0a : FSpec _
  SPEC (ps : ptr * ptr) 'n [vptr (fst ps) ~> n] [] True
  '(_ : unit) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0a : m_body spec_a0a := fun ps =>
  'v0 <- let (p0, _) := ps in Read p0;
  Ret tt.
Goal f_body_match vprog_a0a (m_spec spec_a0a).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a0a.
Proof. Tac.erase_impl. Defined.


Definition spec_a0b : FSpec _
  SPEC (ps : ptr * ptr) 'n [vptr (fst ps) ~> n] [] True
  '(_ : memdata) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0b : m_body spec_a0b := fun ps =>
  let (p0, _) := ps in
  Read p0.
Goal f_body_match vprog_a0b (m_spec spec_a0b).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a0b.
Proof. Tac.erase_impl. Defined.


Definition spec_a0c : FSpec _
  SPEC (ns : nat * nat) '(v0, v1) [] [vdummy (Fin.t (fst ns)) ~> v0; vdummy (Fin.t (snd ns)) ~> v1] True
  '(_ : unit) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0c : m_body spec_a0c := fun ns =>
  let (n0, n1) := ns in
  gLem remove_vdummy (Fin.t n0);;
  gLem remove_vdummy (Fin.t n1).
Goal f_body_match vprog_a0c (m_spec spec_a0c).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.
Goal f_erase vprog_a0c.
Proof. Tac.erase_impl. Defined.


Definition spec_a0d : FSpec _
  SPEC (ns : nat * nat) & (_ : Fin.t (fst ns)) 'v [] [vdummy (Fin.t (snd ns)) ~> v] True
  '(r : nat) & (_ : Fin.t r) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0d : m_body spec_a0d := fun ns g =>
  (let (n0, n1) as ns return Fin.t (fst ns) -> _ := ns in fun g =>
   gLem remove_vdummy (Fin.t n1);;
   RetG n0 g) g.
Goal f_body_match vprog_a0d (m_spec spec_a0d).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.
Goal f_erase vprog_a0d.
Proof. Tac.erase_impl. Defined.


Definition spec_a0e : FSpec _
  SPEC (ns : nat * nat) & (_ : Fin.t (fst ns) * Fin.t (snd ns)) 'tt [] [] True
  '(_ : nat) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a0e : m_body spec_a0e := fun ns gs =>
  let (g0, g1) := gs in
  (let (n0, n1) as ns return Fin.t (fst ns) -> Fin.t (snd ns) -> _ := ns in fun g0 g1 =>
   Ret n0) g0 g1.
Goal f_body_match vprog_a0e (m_spec spec_a0e).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.
Goal f_erase vprog_a0e.
Proof. Tac.erase_impl. Defined.

(* branch *)

Definition spec_a1a : FSpec _
  SPEC ((b, p0, p1, p2) : bool * ptr * ptr * ptr)
  '(n0, n1, n2) [vptr p0 ~> n0] [vptr p1 ~> n1; vptr p2 ~> n2] True
  '(_ : unit) (n1', n2') [vptr p1 ~> n1'; vptr p2 ~> n2'] (b = true -> n1' = 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1a : m_body spec_a1a := fun '(b, p0, p1, p2) =>
  if b
  then Write p1 0
  else Write p2 1.
Goal f_body_match vprog_a1a (m_spec spec_a1a).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp; congruence.
Qed.
Goal f_erase vprog_a1a.
Proof. Tac.erase_impl. Defined.


Inductive bool3 : Set := B0 | B1 | B2.

Definition spec_a1b : FSpec _
  SPEC ((b, p) : bool3 * ptr)
  'n [] [vptr p ~> n] (b <> B2)
  '(_ : unit) n' [vptr p ~> n'] (b <> B1 -> n' = 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1b : m_body spec_a1b := fun '(b, p) =>
  match b with
  | B0 => Write p 0
  | B1 | B2 => Ret tt
  end.
Goal f_body_match vprog_a1b (m_spec spec_a1b).
Proof. solve_by_wlp; congruence. Qed.
Goal f_erase vprog_a1b.
Proof. Tac.erase_impl. Defined.


Definition spec_a1c : FSpec _
  SPEC ((o, p) : option nat * ptr)
  'n [] [vptr p ~> n] (n > 0 /\ match o with Some n' => n' > 0 | None => True end)
  '(_ : unit) n' [vptr p ~> n'] (n' > 0).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1c : m_body spec_a1c := fun '(o, p) =>
  match o with
  | Some n => Write p n
  | None   => Ret tt
  end.
Goal f_body_match vprog_a1c (m_spec spec_a1c).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a1c.
Proof. Tac.erase_impl. Defined.


Definition spec_a1d : FSpec _
  SPEC (b : bool)
  'v [] [(if b as b return Vprop.p (if b then nat else bool) then vdummy nat else vdummy bool) ~> v] True
  '(_ : unit) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1d : m_body spec_a1d := fun b =>
  if b
  then gLem remove_vdummy nat
  else gLem remove_vdummy bool.
Goal f_body_match vprog_a1d (m_spec spec_a1d).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a1d.
Proof. Tac.erase_impl. Defined.


Definition spec_a1e : FSpec _
  SPEC (b : bool) & (_ : if b then nat else unit)
  'tt [] [] True
  '(_ : unit) & (_ : option nat) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a1e : m_body spec_a1e := fun b g =>
  (if b as b return (if b then nat else unit) -> _
   then fun g => RetG tt (Some g)
   else fun _ => RetG tt None
  ) g.
Goal f_body_match vprog_a1e (m_spec spec_a1e).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.
Goal f_erase vprog_a1e.
Proof. Tac.erase_impl. Defined.


Definition spec_a2a : FSpec _
  SPEC ((p0, p1) : ptr * ptr)
  '(n0, n1) [vptr p0 ~> n0] [vptr p1 ~> n1] (n0 <= n1)
  '(_ : unit) n1' [vptr p1 ~> n1'] (n0 <= n1').
Proof. Tac.build_FSpec. Defined.

Definition vprog_a2a : m_body spec_a2a := fun '(p0, p1) =>
  'v1 <- Read p1;
  'v0 <- gGet (SLprop.cell p0);
  Assert (fun 'tt => ([], v0 <= v1));;
  Write p1 (S v1).
Goal f_body_match vprog_a2a (m_spec spec_a2a).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a2a.
Proof. Tac.erase_impl. Defined.

Definition vprog_a2b : m_body spec_a2a := fun '(p0, p1) =>
  'v1 v0 <- (
    'v1 <- Read p1;
    'v0 <- gGet (SLprop.cell p0);
    RetG v1 v0);
  Assert (fun 'tt => ([], v0 <= v1));;
  Write p1 (S v1).
Goal f_body_match vprog_a2b (m_spec spec_a2a).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a2b.
Proof. Tac.erase_impl. Defined.


Definition spec_a3a : FSpec _
  SPEC (_ : unit) & ((n0, n1) : nat * nat)
  'tt [] [] True
  '(_ : unit) & (r : nat) tt [] (r = n0 + n1).
Proof. Tac.build_FSpec. Defined.

Definition vprog_a3a : m_body spec_a3a := fun _ '(n0, n1) =>
  RetG tt (n0 + n1).
Goal f_body_match vprog_a3a (m_spec spec_a3a).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a3a.
Proof. Tac.erase_impl. Defined.


Definition spec_a3b : FSpec _
  SPEC ((_, _) : nat * unit) & (_ : nat)
  'tt [] [] True
  '(_ : nat) tt [] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a3b : m_body spec_a3b := fun '(n, _) _ =>
  Ret n.
Goal f_body_match vprog_a3b (m_spec spec_a3b).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a3b.
Proof. Tac.erase_impl. Defined.


Definition spec_a4a : FSpec _
  SPEC ((p0, p1, p2) : ptr * ptr * ptr)
  '(v0, v1) [vptr p2 ~> v1] [vptr p0 ~> v0] (vptr p0 = vptr p1)
  '(_ : unit) tt [vptr p1 ~> v0] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a4a : m_body spec_a4a := fun '(p0, p1, p2) =>
  gRewrite (vptr p0) (vptr p1).
Goal f_body_match vprog_a4a (m_spec spec_a4a).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.
Goal f_erase vprog_a3b.
Proof. Tac.erase_impl. Defined.


Definition spec_a4b : FSpec _
  SPEC ((n0, n1) : nat * nat)
  'v0 [] [vdummy (Fin.t n0) ~> v0] (n0 = n1)
  '(_ : unit) v1 [vdummy (Fin.t n1) ~> v1] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a4b : m_body spec_a4b := fun '(n0, n1) =>
  gRewrite n0 n1.
Goal f_body_match vprog_a4b (m_spec spec_a4b).
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.


Definition spec_a5a : FSpec _
  SPEC (p : ptr)
  'v [] [vptr p ~> v] True
  '(p' : ptr) tt [vptr p' ~> v] True.
Proof. Tac.build_FSpec. Defined.

Definition vprog_a5a : m_body spec_a5a := fun p =>
  't <- Ret p;
  Ret p.
Goal f_body_match vprog_a5a (m_spec spec_a5a).
Proof. solve_by_wlp. Qed.

End Test.
