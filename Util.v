Require Import Coq.Setoids.Setoid.


(* Relation classes *)

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

Ltac auto_tc := auto with typeclass_instances.

Module Rel.
  Section Conj.
    Context [A] (R0 R1 : relation A).

    Definition conj : relation A := relation_conjunction R0 R1.
    
    Global Instance conj_Equivalence {E0 : Equivalence R0} {E1 : Equivalence R1}: Equivalence conj.
    Proof.
      split.
      - intro x; split; reflexivity.
      - intros x y []; split; symmetry; assumption.
      - intros x y z [] []; split; etransitivity; eassumption.
    Qed.

    Global Instance conj_PreOrder {E0 : PreOrder R0} {E1 : PreOrder R1}: PreOrder conj.
    Proof.
      split.
      - intro x; split; reflexivity.
      - intros x y z [] []; split; etransitivity; eassumption.
    Qed.
  End Conj.
  Section Point.
    Context (A : Type) [B : Type] (R : relation B).

    Definition point : relation (A -> B) := Morphisms.pointwise_relation A R.

    Global Instance point_PreOrder {E : PreOrder R}: PreOrder point.
    Proof.
      split.
      - intros x a; reflexivity.
      - intros x y z H0 H1 a; etransitivity; eauto.
    Qed.
  End Point.
  Section Pull.
    Context [A B] (f : A -> B) (R : relation B).
    
    Definition pull : relation A := fun x y => R (f x) (f y).
  
    Global Instance pull_Equivalence {E : Equivalence R}: Equivalence pull.
    Proof.
      unfold pull; constructor; repeat intro.
      - reflexivity.
      - symmetry; auto.
      - etransitivity; eauto.
    Qed.
    
    Global Instance pull_PreOrder {E : PreOrder R}: PreOrder pull.
    Proof.
      unfold pull; constructor; repeat intro.
      - reflexivity.
      - etransitivity; eauto.
    Qed.
  End Pull.

  Global Ltac by_expr E :=
    match goal with
    | |- _ ?R => change R with E; auto using Build_PreOrder with typeclass_instances
    end.
End Rel.


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

(* heterogeneous tuple *)

Module Tuple.
  Fixpoint t (TS : list Type) : Type :=
    match TS with
    | nil       => unit
    | cons T TS => T * t TS
    end.

  (* arrow *)

  Fixpoint arrow (TS : list Type) (TRG : Type) : Type :=
    match TS with
    | nil       => TRG
    | cons T TS => T -> arrow TS TRG
    end.

  Fixpoint arrow_of_fun [TS : list Type] [TRG : Type]:
    (t TS -> TRG) -> arrow TS TRG :=
    match TS as TS' return (t TS' -> TRG) -> arrow TS' TRG with
    | nil       => fun f => f tt
    | cons T TS => fun f x => arrow_of_fun (fun xs => f (x, xs))
    end.

  Fixpoint arrow_to_fun [TS : list Type] [TRG : Type]:
    arrow TS TRG -> (t TS -> TRG) :=
    match TS as TS' return arrow TS' TRG -> (t TS' -> TRG) with
    | nil       => fun f _  => f
    | cons T TS => fun f xs => let (x, xs) := xs in arrow_to_fun (f x) xs
    end.

  Lemma arrow_to_of [TS : list Type] [TRG : Type] (f : t TS -> TRG) (x : t TS):
    arrow_to_fun (arrow_of_fun f) x = f x.
  Proof.
    induction TS; destruct x; simpl; auto.
    apply IHTS.
  Qed.

  (* forall *)

  Fixpoint all (TS : list Type) : (t TS -> Prop) -> Prop :=
    match TS as TS' return (t TS' -> Prop) -> Prop with
    | nil       => fun P => P tt
    | cons T TS => fun P => forall (x : T), all TS (fun xs => P (x, xs))
    end.

  Lemma all_iff TS P:
    all TS P <-> forall xs : t TS, P xs.
  Proof.
    induction TS; simpl; [|setoid_rewrite IHTS];
      (split; [intros H []; apply H | auto]).
  Qed.

  (* exists *)
  
  Fixpoint ex (TS : list Type) : (t TS -> Prop) -> Prop :=
    match TS as TS' return (t TS' -> Prop) -> Prop with
    | nil       => fun P => P tt
    | cons T TS => fun P => exists (x : T), ex TS (fun xs => P (x, xs))
    end.
  
  Lemma ex_iff TS P:
    ex TS P <-> exists xs : t TS, P xs.
  Proof.
    induction TS; simpl; [|setoid_rewrite IHTS];
      (split; intro H; [decompose record H|case H as [[]]]; eauto).
  Qed.
End Tuple.

