Require Import SLFun.ConcreteProg.

Definition f_aux  : fid := 0.
Definition f_main : fid := 1.

Definition s_aux : f_spec := {|
  fs_arg_t := ptr;
  fs_ret_t := nat;
  fs_pre   := fun p m => Mem.read m p > 0;
  fs_post  := fun p m0 r m1 => Mem.read m1 p = S r;
|}.

Definition s_main : f_spec := {|
  fs_arg_t := unit;
  fs_ret_t := unit;
  fs_pre   := fun _ _ => True;
  fs_post  := fun _ _ _ _ => True;
|}.

Inductive Sctx : scontext :=
  | Sctx_aux  : Sctx f_aux  s_aux
  | Sctx_main : Sctx f_main s_main.

Definition i_aux : f_impl := {|
  f_arg_t := ptr;
  f_ret_t := nat;
  f_body  := fun p =>
    Bind (Read p) (fun x => Ret (pred x))
|}.

Definition ptr0 : ptr := 42.
Global Opaque ptr0.

Definition i_main : f_impl := {|
  f_arg_t := unit;
  f_ret_t := unit;
  f_body  := fun _ =>
    Bind (Write ptr0 3) (fun _ =>
    Bind (Call nat f_aux ptr0) (fun r =>
          Assert (fun m => Mem.read m ptr0 = S r)))
|}.

Definition Cctx : context :=
  fun f => match f with
  | 0 => Some i_aux
  | 1 => Some i_main
  | _ => None
  end.

Lemma match_aux:
  f_match_spec Sctx i_aux s_aux.
Proof.
  constructor; intros p m; simpl.
  case (Mem.read m p); simpl; try reflexivity.
  inversion 1.
Qed.

Lemma match_main:
  f_match_spec Sctx i_main s_main.
Proof.
  constructor; intros _ m _; simpl.
  do 3 esplit. constructor.
  simpl.
  split.
    { unfold Mem.read, Mem.write; destruct Mem.ptr_eq.
      repeat constructor. congruence. }
  auto.
Qed.

Lemma match_context:
  context_match_spec Cctx Sctx.
Proof.
  inversion 1; simpl; (do 2 esplit; [reflexivity|]).
  apply match_aux.
  apply match_main.
Qed.

Lemma context_oracle_free:
  context_oracle_free Cctx.
Proof.
  intros [|[|]] fi; simpl; simplify_eq 1; intros <- ?;
  repeat constructor.
Qed.
