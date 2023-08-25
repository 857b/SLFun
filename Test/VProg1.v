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

Definition m_body [sg sgh e] (F : @FSpec.of_exp (@CP.ghost_sg sg sgh) e) : Type := f_body CT sgh.

Inductive Test [sg sgh]
  (e : @FSpec.t_exp (@CP.ghost_sg sg sgh))
  (b : CP.opt_sigG_arrow (CP.f_ghin_t sgh) (fun _ => instr CT (CP.f_retgh_t sgh))) : Prop :=
  mk_test_fun
    (S : @FSpec.of_exp (@CP.ghost_sg sg sgh) e)
    (E : f_erase (CP.opt_sigG_to_fun b))
    (M : f_body_match (CP.opt_sigG_to_fun b) (FSpec.m_spec S)).
Arguments Test _ _ e%vprog_spec.

Ltac init_Test :=
  unshelve eexists; [ Tac.build_of_exp | Tac.erase_impl | cbn ].


Goal Test SPEC (p : ptr)
  'n [vptr p ~> n] [] True
  '(r : nat) tt [] True
(fun _ =>
  Ret 42).
Proof.
  init_Test.
  solve_by_wlp.
Qed.

Goal Test SPEC (p : ptr)
  'n [] [vptr p ~> n] True
  '(p' : ptr) tt [vptr p' ~> n] True
(fun p =>
  'p1 <- Ret p (pt := fun p => [vptr p~>]);
  Ret p1 (pt := fun p => [vptr p~>])).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal forall (p : ptr) (n : memdata), exists s f,
  HasSpec CT
    ('p1 <- Ret p (pt := fun p => [vptr p~>]);
     Ret p1 (pt := fun p => [vptr p~>]))
    [vptr p ~> n]
    s f /\
  Tac.display f.
Proof.
  do 3 eexists. {
    Tac.build_HasSpec Tac.post_hint_None.
  }
  split.
Qed.

Section DLet. (* destructive let *)

Goal Test SPEC ((ps, p1) : (ptr * ptr) * ptr)
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

Goal Test SPEC (ps : ptr * ptr)
  'n [vptr (fst ps) ~> n] [] True
  '(_ : unit) tt [] True
(fun ps =>
  'v0 <- let (p0, _) := ps in Read p0;
  Ret tt).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC (ps : ptr * ptr)
  'n [vptr (fst ps) ~> n] [] True
  '(_ : memdata) tt [] True
(fun ps =>
  let (p0, _) := ps in
  Read p0).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC (ns : nat * nat)
  '(v0, v1) [] [vdummy (Fin.t (fst ns)) ~> v0; vdummy (Fin.t (snd ns)) ~> v1] True
  '(_ : unit) tt [] True
(fun ns =>
  let (n0, n1) := ns in
  gLem remove_vdummy (Fin.t n0);;
  gLem remove_vdummy (Fin.t n1)).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC (ns : nat * nat) & (_ : Fin.t (fst ns))
  'v [] [vdummy (Fin.t (snd ns)) ~> v] True
  '(r : nat) & (_ : Fin.t r) tt [] True
(fun ns g =>
  (let (n0, n1) as ns return Fin.t (fst ns) -> _ := ns in fun g =>
   gLem remove_vdummy (Fin.t n1);;
   RetG n0 g) g).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC (ns : nat * nat) & (_ : Fin.t (fst ns) * Fin.t (snd ns))
  'tt [] [] True
  '(_ : nat) tt [] True
(fun ns gs =>
  let (g0, g1) := gs in
  (let (n0, n1) as ns return Fin.t (fst ns) -> Fin.t (snd ns) -> _ := ns in fun g0 g1 =>
   Ret n0) g0 g1).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

End DLet.

Section Branch.

Goal Test SPEC ((b, p0, p1, p2) : bool * ptr * ptr * ptr)
  '(n0, n1, n2) [vptr p0 ~> n0] [vptr p1 ~> n1; vptr p2 ~> n2] True
  '(_ : unit) (n1', n2') [vptr p1 ~> n1'; vptr p2 ~> n2'] (b = true -> n1' = 0)
(fun '(b, p0, p1, p2) =>
  if b
  then Write p1 0
  else Write p2 1).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp; congruence.
Qed.

Inductive bool3 : Set := B0 | B1 | B2.

Goal Test SPEC ((b, p) : bool3 * ptr)
  'n [] [vptr p ~> n] (b <> B2)
  '(_ : unit) n' [vptr p ~> n'] (b <> B1 -> n' = 0)
(fun '(b, p) =>
  match b with
  | B0 => Write p 0
  | B1 | B2 => Ret tt
  end).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp; congruence.
Qed.

Goal Test SPEC ((o, p) : option nat * ptr)
  'n [] [vptr p ~> n] (n > 0 /\ match o with Some n' => n' > 0 | None => True end)
  '(_ : unit) n' [vptr p ~> n'] (n' > 0)
(fun '(o, p) =>
  match o with
  | Some n => Write p n
  | None   => Ret tt
  end).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC (b : bool)
  'v [] [(if b as b return Vprop.p (if b then nat else bool) then vdummy nat else vdummy bool) ~> v] True
  '(_ : unit) tt [] True
(fun b =>
  if b
  then gLem remove_vdummy nat
  else gLem remove_vdummy bool).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC (b : bool) & (_ : if b then nat else unit)
  'tt [] [] True
  '(_ : unit) & (_ : option nat) tt [] True
(fun b g =>
  (if b as b return (if b then nat else unit) -> _
   then fun g => RetG tt (Some g)
   else fun _ => RetG tt None
  ) g).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

End Branch.


Definition spec_a2a : FSpec.of_exp
  SPEC ((p0, p1) : ptr * ptr)
  '(n0, n1) [vptr p0 ~> n0] [vptr p1 ~> n1] (n0 <= n1)
  '(_ : unit) n1' [vptr p1 ~> n1'] (n0 <= n1').
Proof. Tac.build_of_exp. Defined.

Definition vprog_a2a : m_body spec_a2a := fun '(p0, p1) =>
  'v1 <- Read p1;
  'v0 <- gGet (SLprop.cell p0);
  Assert (fun 'tt => ([], v0 <= v1));;
  Write p1 (S v1).
Goal f_body_match vprog_a2a (FSpec.m_spec spec_a2a).
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
Goal f_body_match vprog_a2b (FSpec.m_spec spec_a2a).
Proof. solve_by_wlp. Qed.
Goal f_erase vprog_a2b.
Proof. Tac.erase_impl. Defined.


Goal Test SPEC (_ : unit) & ((n0, n1) : nat * nat)
  'tt [] [] True
  '(_ : unit) & (r : nat) tt [] (r = n0 + n1)
(fun _ '(n0, n1) =>
  RetG tt (n0 + n1)).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC ((_, _) : nat * unit) & (_ : nat)
  'tt [] [] True
  '(_ : nat) tt [] True
(fun '(n, _) _ =>
  Ret n).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.


Goal Test SPEC ((p0, p1, p2) : ptr * ptr * ptr)
  '(v0, v1) [vptr p2 ~> v1] [vptr p0 ~> v0] (vptr p0 = vptr p1)
  '(_ : unit) tt [vptr p1 ~> v0] True
(fun '(p0, p1, p2) =>
  gRewrite (vptr p0) (vptr p1)).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Goal Test SPEC ((n0, n1) : nat * nat)
  'v0 [] [vdummy (Fin.t n0) ~> v0] (n0 = n1)
  '(_ : unit) v1 [vdummy (Fin.t n1) ~> v1] True
(fun '(n0, n1) =>
  gRewrite n0 n1).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.


Goal Test SPEC (p : ptr)
  'v [] [vptr p ~> v] True
  '(p' : ptr) tt [vptr p' ~> v] True
(fun p =>
  't <- Ret p;
  Ret p).
Proof.
  init_Test.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

End Test.
