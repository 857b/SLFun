From SLFun Require Import Util Values SL VProg.Main.

Import Util.List.
Import SLNotations ListNotations VProg.Main.Notations FunProg.Notations.

Section Test.
  Variable CT : ConcreteProg.context.

Definition N := 2(*PLACEHOLDER*).

Definition Test_spec : FDecl SPEC
  ((p0, p1) : ptr * ptr)
  '(n,n1) [vptr p1 ~> n1] [vptr p0 ~> n] True
  '(p : ptr) tt [vptr p ~> n] True.
Proof. Derived. Defined.
Variable Test : Test_spec CT.

Definition Test_impl : FImpl Test := fun '(p0, _) =>
  Nat.iter N (A := ptr -> instr CT ptr) (fun k p =>
    'x <- Ret p (pt := fun p => [vptr p~>]);
    k x)
    (fun p => Ret p) p0.

Lemma Test_correct : FCorrect Test_impl.
Proof.
  time "tactics" (
  intro;
  time "build_impl_match" Tac.build_impl_match;
  time "simpl_prog_1" FunProg.simpl_prog;
  time "simpl_prog_2" FunProg.simpl_prog;
  time "build_wlp"    FunProg.by_wlp;
  time "solve_wlp"    FunProg.solve_wlp).
Time Qed.

End Test.
