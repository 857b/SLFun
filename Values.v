Require Import SLFun.Util.


Definition ptr : Type := nat.

Definition memdata : Type := nat.

(* TODO: only for non null pointers *)
Definition mem : Type := ptr -> memdata.

Module Mem.
  Definition t := mem.

  Definition read (m : t) (p : ptr) : memdata := m p.

  (* TODO? Stdlib *)
  Fixpoint ptr_eq (p0 p1 : ptr) {struct p0} : {p0 = p1}+{p0<>p1}.
  Proof.
    case p0 as [|p0], p1 as [|p1].
    2,3:right; discriminate 1.
    - left; reflexivity.
    - case (ptr_eq p0 p1); [left|right]; congruence.
  Defined.

  Definition write (m : t) (p : ptr) (x : memdata) : t :=
    fset ptr_eq p x m.
End Mem.

(* Functions and signatures *)

Definition fid : Set := nat.

Record f_sig := mk_f_sig {
  f_arg_t : Type;
  f_ret_t : Type;
}.

Definition sig_context := fid -> option f_sig.
