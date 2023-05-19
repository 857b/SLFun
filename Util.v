From Coq Require Import Setoids.Setoid Lists.List.
From Coq Require Vectors.Vector derive.Derive.

Import ListNotations.


(* Tactics *)

Global Create HintDb DeriveDB discriminated.
Global Hint Constants Opaque : DeriveDB.
Global Hint Variables Opaque : DeriveDB.
Ltac Derived := solve [auto 1 with DeriveDB nocore].

Inductive Arrow (A B : Type) :=
  mk_Arrow (H : A -> B).
Global Arguments mk_Arrow [_ _].

Local Lemma cut_Arrow [goal0 goal1]
  (S : Arrow goal1 goal0)
  (C : goal1):
  goal0.
Proof. apply S, C. Defined.

(* solves a goal [Arrow ?A B]
   [tc] should solve [B] possibly leaving a single goal [H].
   In this case, [?A] is instantiated to [H]. Otherwise, [?A] is unchanged. *)
Ltac mk_Arrow_tac tc :=
  constructor;
  let H := fresh "H" in intro H;
  tc tt;
  exact H.

(* DB for [Intro].
   Should solve goals [Arrow ?goal1 goal0] and instantiate [?goal1] to [forall _, _] *)
Global Create HintDb IntroDB discriminated.
Global Hint Constants Opaque : IntroDB.
Global Hint Variables Opaque : IntroDB.

Ltac Intro_core :=
  refine (cut_Arrow _ _); [ solve [eauto 1 with IntroDB nocore] |].

Global Tactic Notation "Intro" :=
  Intro_core; intro.

Global Tactic Notation "Intro" simple_intropattern(x) :=
  Intro_core; intros x.

(* DB for [Apply].
   Should solve goals [Arrow ?goal1 goal0] and instantiate [?goal1] to [{_ & _}] *)
Global Create HintDb ApplyDB discriminated.
Global Hint Constants Opaque : ApplyDB.
Global Hint Variables Opaque : ApplyDB.

Ltac Apply_core := 
  refine (cut_Arrow _ _); [ solve [eauto 1 with ApplyDB nocore] |].

Global Tactic Notation "Apply" :=
  Apply_core; unshelve eexists.

Global Tactic Notation "Apply" uconstr(x) :=
  Apply_core; exists x.

Global Tactic Notation "EApply" :=
  Apply_core; eexists.

Global Tactic Notation "EApply" uconstr(x) :=
  Apply_core; eexists x.


Module Tac.
  Module Notations.
    Global Tactic Notation "dummy_goal" uconstr(G) :=
      let D := fresh "Dummy" in
      unshelve eassert G as D;
      [..|clear D].
  End Notations.
  Export Notations.

  Ltac cbn_refl := cbn; repeat intro; reflexivity.

  Ltac build_term t build :=
    dummy_goal (t = _);
    [ build tt | reflexivity | ].

  (* fails iff [f] succeeds (or fail with level > 0) *)
  Ltac inv_fail f :=
    try (f; gfail 1).

  (* executes [f] and reverts its effects, keeping its failure *)
  Ltac revert_exec f :=
   inv_fail ltac:(inv_fail f).

  (* detects inductive terms whith only one case *)
  Ltac is_single_case x :=
    revert_exec ltac:(assert (x = x); [clear; case x; [ ]; constructor|]).

  (* detects inductive terms whith only one case and no arguments *)
  Ltac is_unit_case x :=
    Tac.revert_exec ltac:(assert (x = x); [clear; case x; [ ]; Tac.inv_fail intro; constructor|]).

  Ltac nondep_case t :=
    lazymatch goal with |- ?g =>
    let gl := fresh "GOAL" in
    set (gl := g);
    case t;
    unfold gl; clear gl
    end.

  Ltac const_case t :=
    lazymatch goal with |- ?g =>
    let gl := fresh "GOAL" in
    set (gl := g);
    case t;
    repeat match goal with |- forall _, _ => intros _ end;
    unfold gl; clear gl
    end.


  Lemma apply_Arrow_lem [H0 H1]
    (C : Arrow H0 H1):
    H0 -> H1.
  Proof.
    apply C.
  Defined.

  Ltac apply_Arrow H :=
    eapply apply_Arrow_lem in H; cycle 1.


  (* given [u := x0 :: ... :: x9 :: tail], call [f tail] *)
  Ltac elist_tail u f :=
    let rec iter u :=
      lazymatch u with
      | cons _ ?u => iter u
      | _         => f u
      end
    in iter u.

  (* given [u := x0 :: ... :: x9 :: ?tail], instantiate [?tail] to [x :: ?tail'] *)
  Ltac elist_add u x :=
    elist_tail u ltac:(fun tail =>
    build_term tail ltac:(fun _ => refine (cons x _); shelve)).

  (* given [u := x0 :: ... :: x9 :: ?tail], instantiate [?tail] to [nil] *)
  Ltac elist_end u :=
    elist_tail u ltac:(fun tail =>
    build_term tail ltac:(fun _ => refine nil)).
End Tac.

(* Optional argument *)

Class opt_arg (A : Type) (def : A) := get_opt_arg : A.
Global Instance opt_arg_def {A def} : opt_arg A def := def.

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
    | |- _ ?R =>
        change R with E;
        auto  using Build_PreOrder with typeclass_instances;
        eauto using Build_PreOrder with typeclass_instances
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


(* Extensions of the Coq libraries *)

Module List.
  Include Coq.Lists.List.

  Fixpoint mapi [A B : Type] (f : nat -> A -> B) (u : list A) : list B :=
    match u with
    | nil     => nil
    | x :: xs => f O x :: mapi (fun i => f (S i)) xs
    end.

  (* Transparent lemmas *)

  Module Transp.
    Lemma map_length [A B] (f : A -> B) (l : list A):
      length (map f l) = length l.
    Proof.
      induction l; cbn; f_equal; auto.
    Defined.

    Lemma map_map [A B C] (f : A -> B) (g : B -> C) (l : list A):
      map g (map f l) = map (fun x => g (f x)) l.
    Proof.
      induction l; simpl; f_equal; auto.
    Defined.

    Lemma map_app [A B] (f : A -> B) (u v : list A):
      map f (u ++ v) = map f u ++ map f v.
    Proof.
      induction u; simpl; f_equal; auto.
    Defined.
  End Transp.
End List.

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

  (* Tactic *)

  Global Ltac build_shape :=
    repeat (refine (Vector.cons _ _ _ _); [shelve|]); exact (Vector.nil _).
End Vector.

(* propositions *)

Lemma exists_eq_const [A : Type] (P : A -> Prop) (x0 : A)
  (C : forall x, P x -> x = x0):
  (exists x, P x) <-> P x0.
Proof.
  split; eauto.
  intros [x H].
  case (C x H).
  exact H.
Qed.

Definition and_list : list Prop -> Prop :=
  List.fold_right and True.

Lemma and_list_rev (u : list Prop):
  and_list (rev u) <-> and_list u.
Proof.
  unfold and_list.
  enough (IH : forall P, fold_right and P (rev u) <-> fold_right and True u /\ P).
  rewrite IH; tauto.
  induction u; intro; simpl.
  - tauto.
  - rewrite fold_right_app, IHu; simpl; tauto.
Qed.

Definition elim_and_list_f (u : list Prop) (P : Prop) : Prop :=
  List.fold_right (fun (asm goal : Prop) => asm -> goal) P u.

Lemma elim_and_list (u : list Prop) (P : Prop):
  elim_and_list_f u P <-> (and_list u -> P).
Proof.
  induction u; simpl.
  - tauto.
  - rewrite IHu; tauto.
Qed.

Inductive and_list_eq (u v : list Prop) : Prop :=
  and_list_eqI (E : and_list u <-> and_list v).

Lemma simpl_and_list_0 : and_list_eq nil nil.
Proof. constructor; reflexivity. Qed.

Lemma simpl_and_list_r1 [x : Prop] [xs ys]
  (pf : x)
  (E : and_list_eq xs ys):
  and_list_eq (x :: xs) ys.
Proof.
  constructor; simpl.
  case E as [->]; tauto.
Qed.

Lemma simpl_and_list_m1 [x y : Prop] [xs ys]
  (E0 : x <-> y)
  (E1 : and_list_eq xs ys):
  and_list_eq (x :: xs) (y :: ys).
Proof.
  constructor; simpl.
  case E1 as [->]; tauto.
Qed.

Lemma simpl_and_list_e1 [x : Prop] [xs ys]
  (E : and_list_eq xs ys):
  and_list_eq (x :: xs) (x :: ys).
Proof.
  apply simpl_and_list_m1; tauto.
Qed.

(* optional type *)

Module OptTy.
  Definition p := option Type.

  Definition t (P : p) : Type :=
    match P with
    | Some T => T
    | None   => unit
    end.

  Definition arrow (P : p) : forall (TRG : t P -> Type), Type :=
    match P with
    | Some T => fun TRG => forall x : T, TRG x
    | None   => fun TRG => TRG tt
    end.

  Definition of_fun [P] : forall [TRG : t P -> Type] (f : forall x : t P, TRG x), arrow P TRG :=
    match P with
    | Some T => fun TRG f x => f x
    | None   => fun TRG f   => f tt
    end.
  
  Definition to_fun [P] : forall [TRG : t P -> Type] (f : arrow P TRG) (x : t P), TRG x :=
    match P with
    | Some T => fun TRG f  x  => f x
    | None   => fun TRG f 'tt => f
    end.

  Definition to_fun' [P TRG] : forall (f : arrow P (fun _ => TRG)) (x : t P), TRG :=
    match P with
    | Some T => fun f x => f x
    | None   => fun f _ => f
    end.

  Lemma to_of_fun [P TRG] (f : forall x : t P, TRG x) (x : t P):
    to_fun (of_fun f) x = f x.
  Proof.
    destruct P; cbn; [|destruct x]; reflexivity.
  Qed.
End OptTy.

(* heterogeneous tuple *)

Definition type_iso (A B : Type) (f : A -> B) (g : B -> A) : Prop :=
  (forall x : A, g (f x) = x) /\ (forall y : B, f (g y) = y).

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

  Fixpoint of_fun [TS : list Type] {struct TS}:
    forall [TRG : t TS -> Type] (f : forall x : t TS, TRG x), arrow TS TRG :=
    match TS as TS return forall (TRG : t TS -> Type) (f : forall x : t TS, TRG x), arrow TS TRG with
    | nil       => fun TRG f => f tt
    | cons T TS => fun TRG f x => of_fun (fun xs => f (x, xs))
    end.

  Fixpoint to_fun [TS : list Type] {struct TS}:
    forall [TRG : t TS -> Type] (f : arrow TS TRG) (x : t TS), TRG x.
  Proof.
    case TS as [|T TS].
    - intros TRG f [].      exact f.
    - intros TRG f (x, xs). exact (to_fun TS (fun xs => TRG (x, xs)) (f x) xs).
  Defined.

  Lemma to_of_fun [TS : list Type] [TRG : t TS -> Type] (f : forall x : t TS, TRG x) (x : t TS):
    to_fun (of_fun f) x = f x.
  Proof.
    induction TS; destruct x; simpl; auto.
    apply (IHTS (fun xs => TRG (a0, xs))).
  Qed.

  Definition force_match [A] (TS : list Type) (f : Tuple.t TS -> A) (x : Tuple.t TS) : A :=
    to_fun (of_fun f) x.
  Global Arguments force_match/.


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

  (* map *)

  Fixpoint map [A : Type] (F0 : A -> Type) (F1 : A -> Type) (f : forall x : A, F0 x -> F1 x)
    (x : list A) {struct x} : Tuple.t (List.map F0 x) -> Tuple.t (List.map F1 x).
  Proof.
    case x as [|x xs].
    - exact (fun _ => tt).
    - exact (fun '(y, ys) => (f x y, map A F0 F1 f xs ys)).
  Defined.

  (* isomorphisms *)

  Definition type_iso_tu (A : Type) (TS : list Type) :=
    type_iso A (t TS).
  
  Lemma type_iso_tu_nil:
    type_iso_tu unit nil (fun _ => tt) (fun _ => tt).
  Proof.
    split; intros []; reflexivity.
  Qed.

  Lemma type_iso_tu_one A:
    type_iso_tu A [A] (fun x => (x, tt)) (fun '(x, _) => x).
  Proof.
    split.
    - reflexivity.
    - intros (?, []); reflexivity.
  Qed.

  (* NOTE: [_ * _] is left associative but [Tuple.t] is right associative *)
  Lemma type_iso_tu_prod A AS f g B
    (H : type_iso_tu A AS f g):
    type_iso_tu (A * B) (B :: AS) (fun '(xs, x) => (x, f xs)) (fun '(x, xs) => (g xs, x)).
  Proof.
    split.
    - intros (xs, x); rewrite (proj1 H); reflexivity.
    - intros (x, xs); rewrite (proj2 H); reflexivity.
  Qed.

  (* reversing *)

  Fixpoint iso_rev_f (TS0 TS1 : list Type) {struct TS0} : (t TS0 * t TS1) -> t (List.rev_append TS0 TS1).
  Proof.
    case TS0 as [|T TS0]; simpl.
    - exact (fun '(_, x1) => x1).
    - exact (fun '(x, x0, x1) => iso_rev_f _ (cons T TS1) (x0, (x, x1))).
  Defined.

  Fixpoint iso_rev_g (TS0 TS1 : list Type) {struct TS0} : t (List.rev_append TS0 TS1) -> t TS0 * t TS1.
  Proof.
    case TS0 as [|T TS0]; simpl.
    - exact (fun x1 => (tt, x1)).
    - intros [x0 (x, x1)]%iso_rev_g.
      exact (x, x0, x1).
  Defined.

  Lemma type_iso_rev (TS0 TS1 : list Type):
    type_iso (t TS0 * t TS1) (t (List.rev_append TS0 TS1)) (iso_rev_f TS0 TS1) (iso_rev_g TS0 TS1).
  Proof.
    split; revert TS1; induction TS0 as [|T TS0]; simpl; intro.
    - intros ([], ?); reflexivity.
    - intros ((x, x0), x1); rewrite IHTS0; reflexivity.
    - reflexivity.
    - intro y.
      specialize (IHTS0 (cons T TS1) y).
      destruct iso_rev_g as (?, (?, ?)).
      exact IHTS0.
  Qed.

  (* isomorphic user-friendly type *)

  Fixpoint concise_r_t (T0 : Type) (TS : list Type) : Type :=
    match TS with
    | nil     => T0
    | T :: TS => concise_r_t T TS * T0
    end.

  Fixpoint of_concise_r [T0 : Type] [TS : list Type] {struct TS}: concise_r_t T0 TS -> T0 * t TS :=
    match TS with
    | nil     => fun x0        => (x0, tt)
    | T :: TS => fun '(xs, x0) => let '(x, xs) := @of_concise_r T TS xs in (x0, (x, xs))
    end.
  
  Fixpoint to_concise_r [T0 : Type] [TS : list Type] {struct TS}: T0 * t TS -> concise_r_t T0 TS :=
    match TS with
    | nil     => fun '(x0,  _) => x0
    | T :: TS => fun '(x0, xs) => (@to_concise_r T TS xs, x0)
    end.

  Lemma type_iso_concise_r T0 TS:
    type_iso (concise_r_t T0 TS) (T0 * t TS) (@of_concise_r T0 TS) (@to_concise_r T0 TS).
  Proof.
    split; revert T0; induction TS as [|T TS]; intro; cbn.
    - reflexivity.
    - intros (x, x0).
      specialize (IHTS _ x).
      destruct of_concise_r; f_equal; auto.
    - intros [? []]; reflexivity.
    - intros (x0, (x, xs)); rewrite IHTS; reflexivity.
  Qed.

  Definition concise_t (TS : list Type) : Type :=
    match TS with
    | nil     => unit
    | T :: TS => concise_r_t T TS
    end.

  Definition of_concise [TS] : concise_t TS -> t TS.
  Proof.
    unfold concise_t.
    case TS as [|].
    - exact (fun _ => tt).
    - exact (@of_concise_r _ _).
  Defined.
  
  Definition to_concise [TS] : t TS -> concise_t TS.
  Proof.
    unfold concise_t.
    case TS as [|].
    - exact (fun _ => tt).
    - exact (@to_concise_r _ _).
  Defined.

  Definition type_iso_concise TS:
    type_iso (concise_t TS) (t TS) (@of_concise TS) (@to_concise TS).
  Proof.
    case TS as [|T TS].
    - split; intros []; reflexivity.
    - exact (type_iso_concise_r T TS).
  Qed.

  Definition u_t (TS : list Type) : Type :=
    concise_t (List.rev_append TS nil).

  Definition of_u_t [TS] (x : u_t TS) : t TS :=
    fst (iso_rev_g _ _ (of_concise x)).

  Definition to_u_t [TS] (x : t TS) : u_t TS :=
    to_concise (iso_rev_f TS [] (x, tt)).

  Lemma type_iso_u_t TS:
    type_iso (u_t TS) (t TS) (@of_u_t TS) (@to_u_t TS).
  Proof.
    split; intro; unfold of_u_t, to_u_t.
    - specialize (proj2 (type_iso_rev TS []) (of_concise x)).
      case (iso_rev_g _ _ _) as (?, []); cbn; intros ->.
      apply type_iso_concise.
    - ecase type_iso_concise as [_ ->],
            type_iso_rev     as [-> _].
      reflexivity.
  Qed.

  (* equality *)

  (* avoid losing [TS] while reducing [u] and [v] *)
  Inductive typed_eq [TS : list Type] (u v : Tuple.t TS) : Prop :=
    typed_eqI (E : u = v).

  Fixpoint eq_list [TS : list Type] {struct TS}:
    forall (u v : t TS), list Prop.
  Proof.
    case TS as [|T TS].
    - exact (fun _ _ => nil).
    - exact (fun '(x, xs) '(y, ys) => (x = y) :: eq_list TS xs ys).
  Defined.

  Lemma eq_iff_list [TS : list Type] (u v : t TS):
    u = v <-> and_list (eq_list u v).
  Proof.
    induction TS as [|T TS].
    - destruct u, v; simpl; intuition.
    - destruct u as (x, xs), v as (y, ys); simpl; rewrite <- IHTS.
      intuition congruence.
  Qed.

  (* Tactics *)

  Global Ltac build_shape :=
    repeat (refine (pair _ _); [shelve|]); exact tt.
  
  (* replacing a product type with a tuple, given a term that let-matches on the product type *)

  Inductive type_iso_tu_goal [T : Type] (t : T) : forall (P : Prop) (pf : P), Prop :=
    | type_iso_tu_goal_cont [P0 P1 : Prop] (C : P0 -> P1) [pf : P0]:
        type_iso_tu_goal t P0 pf -> type_iso_tu_goal t P1 (C pf)
    | type_iso_tu_goal_end [P : Prop] (pf : P):
        type_iso_tu_goal t P pf.

  Lemma type_iso_tu_init [A TS0 f0 g0 TS1 f1 g1]
    (E : type_iso_tu A (List.rev_append TS0 nil)
                       (fun x => iso_rev_f TS0 nil (f0 x, tt))
                       (fun y => g0 (let (y, _) := iso_rev_g TS0 nil y in y)) ->
         type_iso_tu A TS1 f1 g1)
    (H : type_iso_tu A TS0 f0 g0):
    type_iso_tu A TS1 f1 g1.
  Proof.
    apply E.
    pose proof (R := type_iso_rev TS0 []).
    split.
    - intro x. rewrite (proj1 R), (proj1 H). reflexivity.
    - intro y. rewrite (proj2 H).
      specialize (proj2 R y).
      case iso_rev_g as (?, []); auto.
  Qed.

  Ltac build_type_iso_tu_aux :=
    lazymatch goal with
    (* BUG Coq 8.15.2 in the second test if we reverse the first two cases:
        Anomaly
        "File "pretyping/constr_matching.ml", line 399, characters 14-20: Assertion failed." *)
    | |- type_iso_tu_goal (let 'tt := _ in _) _ _ =>
        refine (type_iso_tu_goal_end _ type_iso_tu_nil)
    | |- type_iso_tu_goal (let (_, _) := ?x in _) _ _ =>
        refine (type_iso_tu_goal_cont _ (type_iso_tu_prod _ _ _ _ _) _);
        destruct x as (?, ?)
    | |- type_iso_tu_goal _ _ _ =>
        refine (type_iso_tu_goal_end _ (type_iso_tu_one _))
    end.

  Ltac build_type_iso_tu :=
    refine (type_iso_tu_goal_cont _ (type_iso_tu_init _) _);
    [ repeat build_type_iso_tu_aux
    | cbn; exact (fun pf => pf) ].

  Module Test.
    Lemma prf_by_type_iso_tu_goal [A T : Type] (f : A -> T) (P : Prop) (pf : P)
      (DUMMY : forall x : A, type_iso_tu_goal (f x) P pf):
      P.
    Proof. exact pf. Qed.

    Definition test_f0' (n0 n1 n2 : nat) := tt.
    Definition test_f0 '(n0, n1, n2) := test_f0' n0 n1 n2.

    Goal exists TS f g,
      type_iso_tu (nat * nat * bool) TS f g /\ TS = TS.
    Proof.
      do 3 eexists. split.
      eapply (prf_by_type_iso_tu_goal test_f0).
      intro x.
      unfold test_f0; cbn.
      build_type_iso_tu.
      reflexivity.
    Qed.
    
    Definition test_f1 'tt := tt.
    
    Goal exists TS f g,
      type_iso_tu unit TS f g /\ TS = TS.
    Proof.
      do 3 eexists. split.
      eapply (prf_by_type_iso_tu_goal test_f1).
      intro x.
      unfold test_f1; cbn.
      build_type_iso_tu.
      reflexivity.
    Qed.
  End Test.

  (* unit *)
  Definition unit : list Type := nil.
  Definition tt : t unit := Datatypes.tt.
End Tuple.

(* dependent tuple *)

Declare Scope dtuple_scope.
Delimit Scope dtuple_scope with dtuple.

Module DTuple.
  Inductive p : Type :=
    | Pnil
    | Pcons (T : Type) (TS : T -> p).

  Fixpoint t (T : p) : Type :=
    match T with
    | Pnil       => Datatypes.unit
    | Pcons T TS => {x : T & t (TS x)}
    end.

  Definition pair [T : Type] [TS : T -> p]
    : forall (x : T) (xs : t (TS x)), {x : T & t (TS x)}
    := existT (fun x => t (TS x)).
  Global Arguments pair _ _ _ _/.

  (* arrow *)

  Fixpoint arrow (T : p) : forall (TRG : t T -> Type), Type :=
    match T with
    | Pnil       => fun TRG =>
        TRG tt
    | Pcons T TS => fun TRG =>
        forall x : T, arrow (TS x) (fun xs => TRG (pair x xs))
    end.

  Fixpoint of_fun [T : p] {struct T}:
    forall [TRG : t T -> Type] (f : forall x : t T, TRG x), arrow T TRG.
  Proof.
    case T as [|T TS]; cbn; intros TRG f.
    - exact (f tt).
    - exact (fun x => of_fun _ _ (fun xs => f (pair x xs))).
  Defined.

  Fixpoint to_fun [T : p] {struct T}:
    forall [TRG : t T -> Type] (f : arrow T TRG) (x : t T), TRG x.
  Proof.
    case T as [|T TS]; cbn; intros TRG f.
    - exact (fun 'tt => f).
    - exact (fun '(existT _ x xs) =>
        to_fun (TS x) (fun xs => TRG (pair x xs)) (f x) xs).
  Defined.

  Lemma to_of_fun [T : p] [TRG : t T -> Type] (f : forall x : t T, TRG x) (x : t T):
    to_fun (of_fun f) x = f x.
  Proof.
    induction T as [|T TS IH]; destruct x; simpl; auto.
    apply (IH _ (fun xs => TRG (pair x xs))).
  Qed.

  (* forall *)

  Fixpoint all (T : p) : (t T -> Prop) -> Prop :=
    match T with
    | Pnil       => fun TRG =>
        TRG tt
    | Pcons T TS => fun TRG =>
        forall x : T, all (TS x) (fun xs => TRG (pair x xs))
    end.

  Lemma all_iff T P:
    all T P <-> forall xs : t T, P xs.
  Proof.
    induction T as [|T TS IH]; simpl; [|setoid_rewrite IH];
      (split; [intros H []; apply H | auto]).
  Qed.

  (* exists *)
  
  Fixpoint ex (T : p) : (t T -> Prop) -> Prop :=
    match T as T' return (t T' -> Prop) -> Prop with
    | Pnil       => fun P => P tt
    | Pcons T TS => fun P => exists x : T, ex (TS x) (fun xs => P (pair x xs))
    end.
  
  Lemma ex_iff T P:
    ex T P <-> exists xs : t T, P xs.
  Proof.
    induction T as [|T TS IH]; simpl; [|setoid_rewrite IH];
      (split; intro H; [decompose record H|case H as [[]]]; eauto).
  Qed.

  (* of tuple *)

  Fixpoint p_tu (TS : list Type) {struct TS} : p :=
    match TS with
    | nil     => Pnil
    | T :: TS => Pcons T (fun _ => p_tu TS)
    end.

  Fixpoint of_tu [TS : list Type] {struct TS} : Tuple.t TS -> t (p_tu TS) :=
    match TS with
    | nil     => fun _        => tt
    | T :: TS => fun '(x, xs) => pair x (of_tu xs)
    end.

  Fixpoint to_tu [TS : list Type] {struct TS} : t (p_tu TS) -> Tuple.t TS :=
    match TS with
    | nil     => fun _                => tt
    | T :: TS => fun '(existT _ x xs) => (x, to_tu xs)
    end.

  Lemma iso_tu (TS : list Type):
    type_iso (Tuple.t TS) (t (p_tu TS)) (@of_tu TS) (@to_tu TS).
  Proof.
    split; induction TS; cbn; intros []; f_equal; auto.
  Qed.
  Definition to_of_tu TS := proj1 (iso_tu TS).

  (* append *)

  Fixpoint p_app (T0 : p) {struct T0} : (t T0 -> p) -> p :=
    match T0 with
    | Pnil       => fun T1 => T1 tt
    | Pcons T TS => fun T1 => Pcons T (fun x => p_app (TS x) (fun xs => T1 (pair x xs)))
    end.

  Fixpoint to_app [T0 : p] {struct T0}:
    forall [T1 : t T0 -> p], {x0 : t T0 & t (T1 x0)} -> t (p_app T0 T1).
  Proof.
    case T0 as [|T TS]; cbn; intros T1 [[] x1].
    - exact x1.
    - refine (pair x (to_app (TS x) (fun xs => T1 (pair x xs)) (existT _ t0 x1))).
  Defined.

  Fixpoint of_app [T0 : p] {struct T0}:
    forall [T1 : t T0 -> p], t (p_app T0 T1) -> {x0 : t T0 & t (T1 x0)}.
  Proof.
    case T0 as [|T TS]; cbn; intros T1.
    - exact (fun x1 => existT _ tt x1).
    - intros [x xs].
      case (of_app (TS x) (fun xs => T1 (pair x xs)) xs) as [x0 x1].
      exists (existT _ x x0).
      exact x1.
  Defined.

  Lemma iso_app (T0 : p) (T1 : t T0 -> p):
    type_iso {x0 : t T0 & t (T1 x0)} (t (p_app T0 T1)) (@to_app T0 T1) (@of_app T0 T1).
  Proof.
    split; induction T0 as [|T TS IH]; cbn.
    - intros [[] ?]; reflexivity.
    - intros [[] ?]; rewrite IH; reflexivity.
    - reflexivity.
    - intros [x xs].
      specialize (IH x _ xs); destruct (of_app xs); rewrite IH.
      reflexivity.
  Qed.

  (* unit *)
  Definition unit : p := Pnil.
  Definition tt : t unit := Datatypes.tt.

  Module Notations.
    Notation "(| x , .. , y |)" := (existT _ x .. (existT _ y Datatypes.tt) .. ) : dtuple_scope.
  End Notations.
End DTuple.

