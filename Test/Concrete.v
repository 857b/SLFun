Require Import SLFun.ConcreteProg.

Definition f_aux  : fid := 0.
Definition f_main : fid := 1.

Definition SIG : sig_context :=
  fun f => match f with
  | 0 => Some (mk_f_sig ptr nat)
  | 1 => Some (mk_f_sig unit unit)
  | _ => None
  end.

Definition ptr0 : ptr := 42.
Global Opaque ptr0.

Definition IMPL : impl_context SIG :=
  fun f => match f with
  | 0 =>
      fun (p : ptr) =>
      Bind (Read p) (fun x => Ret (pred x))
  | 1 =>
      fun (_ : unit) =>
      Bind (Write ptr0 3) (fun _ =>
      Bind (@Call SIG _ f_aux eq_refl ptr0) (fun r =>
            Assert (fun m => Mem.read m ptr0 = S r)))
  | _ => tt
  end.

Definition SPECS : spec_context SIG :=
  fun f => match f with
  | 0 =>
    let sg := mk_f_sig ptr nat in
    fun p : f_arg_t sg => eq {|
      Spec.pre  := fun m       => Mem.read m p > 0;
      Spec.post := fun m0 r m1 => Mem.read m1 p = S r;
    |}
  | 1 =>
    fun _ => eq {|
      Spec.pre  := fun _     => True;
      Spec.post := fun _ _ _ => True;
    |}
  | _ => tt
  end.

Lemma match_context:
  context_match_spec IMPL SPECS.
Proof.
  intros [|[|]]; simpl. 3:constructor.
  all:intros x ? <-; unfold f_match_spec, Spec.wp_impl; revert x; simpl.
  - (* aux *)
    intros p m.
    case (Mem.read m p); simpl; try reflexivity.
    inversion 1.
  - (* main *)
    intros _ m _.
    do 3 esplit; simpl.
    + unfold Mem.read, Mem.write; rewrite Util.fset_gs.
      repeat constructor.
    + auto.
Qed.

Lemma context_oracle_free:
  context_oracle_free IMPL.
Proof.
  intros [|[|]]; simpl; repeat constructor.
Qed.
