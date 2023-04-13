Require Import Coq.Setoids.Setoid.


Local Lemma R_refl [A] (R : relation A) (x y : A) (X : R x x) (E : x = y): R x y.
Proof.
  rewrite <- E; apply X.
Qed.

Ltac reflexivityR := apply R_refl; reflexivity.


Ltac symmetric_iff :=
  let H  := fresh "H"  in
  eassert _ as H; [|
    let Hs := fresh "Hs" in
    pose proof (Hs := H);
    repeat (let x := fresh "x" in intro x;
            refine (_ (Hs x)); clear Hs; intro Hs);
    split; [ exact Hs
           | eapply H; try solve [try symmetry; eassumption] ];
    clear H Hs
  ].

(* [fset] *)

Definition fset [A B : Type] (e : forall (x y : A), {x=y}+{x<>y}) (x : A) (y : B) (f : A -> B) : A -> B :=
  fun x' => if e x' x then y else f x'.

Lemma fset_gs [A B] e x y (f : A -> B):
  fset e x y f x = y.
Proof.
  unfold fset; case e; congruence.
Qed.

Lemma fset_go [A B] e x y (f : A -> B) x'
  (O : x' <> x):
  fset e x y f x' = f x'.
Proof.
  unfold fset; case e; congruence.
Qed.
