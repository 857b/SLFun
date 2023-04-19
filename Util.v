Require Import Coq.Setoids.Setoid.
Require Coq.Vectors.Vector.


(* Relation classes *)

Lemma R_refl [A] (R : relation A) (x y : A) (X : R x x) (E : x = y): R x y.
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

  Fixpoint arrow (TS : list Type) : forall (TRG : t TS -> Type), Type :=
    match TS with
    | nil       => fun TRG => TRG tt
    | cons T TS => fun TRG => forall (x : T), arrow TS (fun xs => TRG (x, xs))
    end.

  Fixpoint arrow_of_fun [TS : list Type] {struct TS}:
    forall [TRG : t TS -> Type] (f : forall x : t TS, TRG x), arrow TS TRG :=
    match TS as TS return forall (TRG : t TS -> Type) (f : forall x : t TS, TRG x), arrow TS TRG with
    | nil       => fun TRG f => f tt
    | cons T TS => fun TRG f x => arrow_of_fun (fun xs => f (x, xs))
    end.

  Fixpoint arrow_to_fun [TS : list Type] {struct TS}:
    forall [TRG : t TS -> Type] (f : arrow TS TRG) (x : t TS), TRG x.
  Proof.
    case TS as [|T TS].
    - intros TRG f [].      exact f.
    - intros TRG f (x, xs). exact (arrow_to_fun TS (fun xs => TRG (x, xs)) (f x) xs).
  Defined.

  Lemma arrow_to_of [TS : list Type] [TRG : t TS -> Type] (f : forall x : t TS, TRG x) (x : t TS):
    arrow_to_fun (arrow_of_fun f) x = f x.
  Proof.
    induction TS; destruct x; simpl; auto.
    apply (IHTS (fun xs => TRG (a0, xs))).
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

(* Extension of the Coq.Vector library *)

Module Vector.
  Include Coq.Vectors.Vector.

  Lemma ext A n (u v : Vector.t A n)
    (E : forall i : Fin.t n, Vector.nth u i = Vector.nth v i):
    u = v.
  Proof.
    apply eq_nth_iff.
    intros ? ? <-; apply E.
  Qed.

  Lemma map_const A B f v n:
    @map A B f n (const v n) = const (f v) n.
  Proof.
    induction n; simpl; f_equal; auto.
  Qed.
  
  Lemma map2_const_l A B C n f u v:
    @map2 A B C f n (const v n) u = map (f v) u.
  Proof.
    induction n; simpl.
    - destruct u using case0.
      reflexivity.
    - destruct u using caseS'.
      simpl; f_equal; auto.
  Qed.
  
  Lemma map2_const_r A B C n f u v:
    @map2 A B C f n u (const v n) = map (fun x => f x v) u.
  Proof.
    induction n; simpl.
    - destruct u using case0.
      reflexivity.
    - destruct u using caseS'.
      simpl; f_equal; auto.
  Qed.
  
  Lemma to_list_inj A n (v0 v1 : t A n)
    (E : to_list v0 = to_list v1):
    v0 = v1.
  Proof.
    induction v0; simpl in *.
    - case v1 using case0. reflexivity.
    - case v1 using caseS'.
      injection E as -> E.
      rewrite (IHv0 _ E).
      reflexivity.
  Qed.
End Vector.
