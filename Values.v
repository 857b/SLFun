Definition ptr : Type := nat.

Definition memdata : Type := nat.

Inductive data_t : Set :=
  | TInt
  | TPtr.

Definition data_ty (t : data_t) : Type :=
  match t with
  | TInt => nat
  | TPtr => ptr
  end.

Definition mem : Type := ptr -> memdata.
