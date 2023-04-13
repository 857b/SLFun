Require Import SLFun.Util.


Definition ptr : Type := nat.
Definition NULL : ptr := O.

Definition memdata : Type := nat.

Definition mem : Type := ptr -> memdata.

Module Mem.
  Definition t := mem.

  Definition read (m : t) (p : ptr) : memdata := m p.

  Definition ptr_eq (p0 p1 : ptr) : {p0 = p1}+{p0<>p1}.
  Proof. decide equality. Defined.

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
