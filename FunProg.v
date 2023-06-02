From SLFun Require Import Util.
From Coq   Require Import Setoids.Setoid.


Module Spec.
  Local Set Implicit Arguments.
  Section WLP.
    Variable A : Type.

    Definition post_t := A -> Prop.
    Definition wp_t   := post_t -> Prop.

    Definition monotone (wp : wp_t) : Prop :=
      forall (post0 post1 : post_t) (LE : forall x, post0 x -> post1 x),
      wp post0 -> wp post1.

    Lemma wp_morph (wp : wp_t) (MONO : monotone wp) (post0 post1 : post_t)
      (POST : forall x, post0 x <-> post1 x):
      wp post0 <-> wp post1.
    Proof.
      split; apply MONO, POST.
    Qed.

    Definition wp_eq (wp0 wp1 : wp_t) : Prop :=
      forall post : post_t, wp0 post <-> wp1 post.

    Global Instance wp_eq_Equivalence : Equivalence wp_eq.
    Proof.
      apply Equivalence.pointwise_equivalence, iff_equivalence.
    Qed.
  End WLP.

  Record t (A : DTuple.p) := mk_t {
    pre_p  : option Prop;
    post_p : option (OptProp.arrow pre_p (fun _ => DTuple.arrow A (fun _ => Prop)));
  }.
  Global Arguments mk_t [A] _ _.

  Definition pre [A] (s : t A) : Prop :=
    OptProp.t (pre_p s).

  Definition post_o [A] (s : t A) (PRE : pre s) (res : DTuple.t A) : option Prop :=
    option_map (fun post => DTuple.to_fun (OptProp.to_fun post PRE) res) (post_p s).

  Definition post [A] (s : t A) (PRE : pre s) (res : DTuple.t A) : Prop :=
    OptProp.t (post_o s PRE res).

  Definition pull_f [A B] (f : DTuple.t A -> DTuple.t B) (s : Spec.t B) : Spec.t A :=
    Spec.mk_t (Spec.pre_p s)
      (option_map (fun post => OptProp.of_fun (fun PRE => DTuple.of_fun (fun x =>
                               DTuple.to_fun (OptProp.to_fun post PRE) (f x))))
                  (Spec.post_p s)).
  Global Arguments pull_f _ _ _ !_/.

  Lemma pull_f_post [A B] f s PRE x:
    post (@pull_f A B f s) PRE x <-> post s PRE (f x).
  Proof.
    unfold pull_f, post, post_o; cbn.
    case post_p as [|]; cbn;
    try rewrite OptProp.to_of_fun, DTuple.to_of_fun;
    reflexivity.
  Qed.
End Spec.


Definition instr (A : DTuple.p) : Type := {wp : Spec.wp_t (DTuple.t A) | Spec.monotone wp}.
Definition wlp [A : DTuple.p] (i : instr A) : Spec.wp_t (DTuple.t A)
  := proj1_sig i.
Definition wlp_monotone [A : DTuple.p] (i : instr A) : Spec.monotone (wlp i)
  := proj2_sig i.

Definition eqv [A : DTuple.p] (p0 p1 : instr A) : Prop :=
  Spec.wp_eq (wlp p0) (wlp p1).

Global Instance eqv_Equivalence A : Equivalence (@eqv A).
Proof.
  Rel.by_expr (Rel.pull (@wlp A) (@Spec.wp_eq _)).
Qed.

Inductive wlpA [A : DTuple.p] (i : instr A) (post : DTuple.arrow A (fun _ => Prop)) : Prop :=
  wlpA_I (P : wlp i (DTuple.to_fun post)).

Lemma wlpA_eqv [pre A i0 i1 post]
  (E : @eqv A i0 i1)
  (C : forall PRE : pre, wlpA i1 (post PRE))
  (PRE : pre) : wlpA i0 (post PRE).
Proof.
  constructor.
  apply E, C.
Qed.


Section Instr.
  Local Obligation Tactic := cbn; intros; do 3 intro; try solve [intuition auto].

  Program Definition Ret [A : DTuple.p] (x : DTuple.t A) : instr A
    := fun post => post x.
  Global Arguments Ret [_] _%dtuple.

  Program Definition Bind [A B : DTuple.p] (f : instr A) (g : DTuple.arrow A (fun _ => instr B)) : instr B
    := fun post => wlp f (fun x => wlp (DTuple.to_fun g x) post).
  Next Obligation.
    apply wlp_monotone; intro; apply wlp_monotone, LE.
  Qed.

  Global Add Parametric Morphism A B : (@Bind A B)
    with signature (@eqv A) ==>
      (Rel.pull (@DTuple.to_fun A (fun _ => instr B))
        (Morphisms.pointwise_relation (DTuple.t A) (@eqv B))) ==>
      @eqv B
    as Bind_morph.
  Proof.
    intros f0 f1 Ef g0 g1 Eg post; cbn.
    etransitivity.
    apply Ef.
    apply Spec.wp_morph. apply wlp_monotone.
    intro; apply Eg.
  Qed.

  Lemma Bind_assoc [A B C] f g h:
    eqv (@Bind B C (@Bind A B f g) h)
        (Bind f (DTuple.of_fun (fun x => Bind (DTuple.to_fun g x) h))).
  Proof.
    intro post; cbn.
    apply Spec.wp_morph. apply wlp_monotone.
    intro x.
    rewrite DTuple.to_of_fun.
    reflexivity.
  Qed.

  Section CallRet.
    Variables (pre : OptProp.p) (A : DTuple.p).

    Definition Call_ret :=
      match pre with
      | Some pre => DTuple.Pcons pre (fun _ => A)
      | None     => A
      end.

    Definition to_Call_ret : OptProp.t pre * DTuple.t A -> DTuple.t Call_ret.
    Proof.
      unfold Call_ret; case pre as [|]; cbn.
      - exact (fun '(PRE, x) => DTuple.pair PRE x).
      - exact (fun '(_, x) => x).
    Defined.

    Definition of_Call_ret : DTuple.t Call_ret -> OptProp.t pre * DTuple.t A.
    Proof.
      unfold Call_ret; case pre as [|]; cbn.
      - intros [PRE x]. exact (PRE, x).
      - exact (fun x => (I, x)).
    Defined.

    Lemma iso_Call_ret :
      type_iso (OptProp.t pre * DTuple.t A) (DTuple.t Call_ret)
        to_Call_ret of_Call_ret.
    Proof.
      unfold Call_ret, to_Call_ret, of_Call_ret.
      split; case pre as [|]; cbn;
      repeat (let x := fresh "x" in intro x; try (case x; clear x)); reflexivity.
    Qed.
  End CallRet.
  Global Arguments to_Call_ret [_ _].
  Global Arguments of_Call_ret [_ _].

  Program Definition Call [A : DTuple.p] (s : Spec.t A)
    : instr (Call_ret (Spec.pre_p s) A)
    := fun post => exists PRE : Spec.pre s, forall x : DTuple.t A,
       Spec.post s PRE x -> post (to_Call_ret (PRE, x)).
  Next Obligation.
    intros [PRE].
    exists PRE; auto.
  Qed.

  Program Definition Assert (P : Prop) : instr DTuple.unit
    := fun post => P /\ post DTuple.tt.

  Program Definition Oracle (A : DTuple.p) : instr A
    := fun post => exists x, post x.
  Next Obligation.
    intros [x]; eauto.
  Qed.

  Program Definition Loop [A B : Type] [C : A + B -> DTuple.p]
    (Inv : DTuple.arrow (DTuple.Pcons (A + B) C) (fun _ => Prop))
    (ini_x : A + B) (ini_y : DTuple.t (C ini_x))
    (f : forall x : A, DTuple.arrow (C (inl x)) (fun _ => instr (DTuple.Pcons (A + B) C)))
    : instr (DTuple.Pcons B (fun x => C (inr x)))
    := fun post =>
       DTuple.to_fun (Inv ini_x) ini_y /\
       (forall (x : A) (y : DTuple.t (C (inl x))),
          DTuple.to_fun (Inv (inl x)) y -> wlp (DTuple.to_fun (f x) y) (DTuple.to_fun Inv)) /\
       (forall (x : B) (y : DTuple.t (C (inr x))),
          DTuple.to_fun (Inv (inr x)) y -> post (DTuple.pair x y)).

  Lemma Loop_morph [A B C Inv ini_x ini_y f0 f1]
    (E : forall (x : A) (y : DTuple.t (C (inl x))),
      eqv (DTuple.to_fun (f0 x) y)
          (DTuple.to_fun (f1 x) y)):
    eqv (@Loop A B C Inv ini_x ini_y f0)
        (@Loop A B C Inv ini_x ini_y f1).
  Proof.
    intro; cbn.
    unfold eqv, Spec.wp_eq in E.
    setoid_rewrite E.
    reflexivity.
  Qed.
End Instr.

(* WLP formula *)

Section WLP_Formula. 
  Inductive wlp_formula [A : DTuple.p] (i : instr A) (f : forall post : DTuple.t A -> Prop, Prop) : Prop :=
    wlp_formulaI (F : forall post, f post -> wlp i post).

  Lemma wlp_formulaE [A i f post] (H : @wlp_formula A i f) (F : f post): wlp i post.
  Proof.
    case H; auto.
  Qed.

  Lemma wlp_formula_imp [A i] f0 [f1 : _ -> Prop]
    (F : wlp_formula i f0)
    (M : forall post, f1 post -> f0 post):
    @wlp_formula A i f1.
  Proof.
    constructor; intros.
    apply F; auto.
  Qed.

  Lemma wlp_formula_Ret [A] x:
    wlp_formula (@Ret A x) (fun post => post x).
  Proof.
    constructor; auto.
  Qed.

  Lemma wlp_formula_Bind [A B f g ff fg]
    (Ff : wlp_formula f ff)
    (Fg : DTuple.arrow A (fun x => wlp_formula (DTuple.to_fun g x) (DTuple.to_fun fg x))):
    wlp_formula (@Bind A B f g)
      (fun post => ff (fun x => DTuple.to_fun fg x post)).
  Proof.
    constructor.
    intros post HF%(wlp_formulaE Ff); simpl.
    eapply wlp_monotone, HF; simpl.
    intros x HG%(wlp_formulaE (DTuple.to_fun Fg x)).
    exact HG.
  Qed.

  Lemma wlp_formula_Call [A] s:
    wlp_formula (@Call A s)
      (fun post =>
        OptProp.ex (Spec.pre_p s) (fun PRE =>
        DTuple.all A (fun x =>
        OptProp.all (Spec.post_o s PRE x) (fun _ =>
        post (to_Call_ret (PRE, x)))))).
  Proof.
    constructor.
    setoid_rewrite OptProp.ex_iff.
    setoid_rewrite DTuple.all_iff.
    setoid_rewrite OptProp.all_iff.
    auto.
  Qed.

  Lemma wlp_formula_Assert P:
    wlp_formula (Assert P) (fun post => P /\ post DTuple.tt).
  Proof.
    constructor; auto.
  Qed.

  Lemma wlp_formula_Oracle A:
    wlp_formula (Oracle A) (fun post => DTuple.ex A post).
  Proof.
    constructor; intro.
    rewrite DTuple.ex_iff; auto.
  Qed.

  Lemma wlp_formula_Loop [A B C Inv ini_x ini_y f ff]
    (Ff : forall x : A, DTuple.arrow (C (inl x)) (fun y =>
      wlp_formula (DTuple.to_fun (f x) y) (DTuple.to_fun (ff x) y))):
    wlp_formula (@Loop A B C Inv ini_x ini_y f)
      (fun post =>
       DTuple.to_fun (Inv ini_x) ini_y /\
       (forall (x : A), DTuple.all (C (inl x)) (fun y =>
          DTuple.to_fun (Inv (inl x)) y -> DTuple.to_fun (ff x) y (DTuple.to_fun Inv))) /\
       (forall (x : B), DTuple.all (C (inr x)) (fun y =>
          DTuple.to_fun (Inv (inr x)) y -> post (DTuple.pair x y)))).
  Proof.
    constructor; intro.
    setoid_rewrite DTuple.all_iff.
    cbn; intuition.
    apply (DTuple.to_fun (Ff x) y); auto.
  Qed.
End WLP_Formula.

(* Must be called on a goal [f a b].
   Destructs the the first occurence of [x] in [a] and [b]. *)
Ltac case_2heads x f a b :=
  let fld0 := fresh "fld" in
  pose (fld0 := f); change (fld0 a b);
  let x0 := fresh "case_x" in
  set (x0 := x) at 1; (* head of [a] *)
  let fld1 := fresh "fld" in
  lazymatch goal with |- fld0 ?a' _ =>
    pose (fld1 := fld0 a'); change (fld1 b)
  end;
  let x1 := fresh "case_x'" in
  set (x1 := x) at 1; (* head of [b] *)
  change x1 with x0;
  unfold fld1, fld0; clear x1 fld0 fld1; clearbody x0;
  refine (elim_boxP _);
  case x0; clear x0;
  cbn; intros;
  constructor.

(* build a formula [match x with ... end] *)
Ltac build_wlp_formula_match build_f x :=
  lazymatch goal with |- wlp_formula _ ?f =>
  Tac.build_term f ltac:(fun _ => intro (* post *); Tac.case_intro_keep x; shelve)
  end;
  cbn;
  lazymatch goal with |- @wlp_formula ?A ?i ?f =>
  case_2heads x (@wlp_formula A) i f
  end;
  build_f.

(* destructive let *)
Ltac build_wlp_formula_dlet build_f x :=
  simple refine (wlp_formula_imp _ _ _);
  [ (* f0 *) destruct x; shelve
  | (* F  *) destruct x; build_f
  | (* M  *)
    intro (* post *);
    let f := fresh "f" in intro f;
    case_eq x;
    exact f ].

(* changes an hypothesis [H : H0 /\ ... /\ H9 /\ L] into [H : L] *)
Ltac conj_proj_last H :=
  repeat lazymatch goal with
  | H : _ /\ _ |- _ => apply proj2 in H
  end.

Ltac build_wlp_formula_branch build_f x :=
  simple refine (wlp_formula_imp _ _ _);
  [ (* f0 *) destruct x; shelve
  | (* F  *) destruct x; build_f
  | (* M  *)
    cbn;
    intro (* post *);
    let f := fresh "f" in intro f;
    case_eq x;
    [ (cbn in f; conj_proj_last f; eapply proj1 in f; exact f) ..
    | cbn in f; conj_proj_last f; exact f] ].

(* solves a goal [wlp_formula i ?f] *)
Ltac build_wlp_formula_ dmatch :=
  let rec build :=
  cbn; clear;
  lazymatch goal with
  | |- wlp_formula (Ret _) _ =>
      refine (wlp_formula_Ret _)
  | |- wlp_formula (Bind _ _) _ =>
      refine (wlp_formula_Bind _ _);
      [ build | cbn; repeat intro; build ]
  | |- wlp_formula (@Call ?A ?s) _ =>
      exact (@wlp_formula_Call A s)
  | |- wlp_formula (Assert _) _ =>
      refine (wlp_formula_Assert _)
  | |- wlp_formula (Oracle _) _ =>
      refine (wlp_formula_Oracle _)
  | |- wlp_formula (Loop _ _ _ _) _ =>
      refine (wlp_formula_Loop _);
      [ cbn; intros; build ]
  | |- wlp_formula (match ?x with _ => _ end) _ =>
      lazymatch dmatch with
      | true =>
          tryif Tac.is_single_case x
          then build_wlp_formula_dlet   build x
          else build_wlp_formula_branch build x
      | false =>
          build_wlp_formula_match build x
      end
  | |- ?g => fail "build_wlp_formula: " g
  end
  in build.

Ltac build_wlp_formula := build_wlp_formula_ false.

Local Lemma by_wlp_lem [pre : Prop] [A] [i : instr A] [post f]
  (F : wlp_formula i f)
  (C : forall PRE : pre, f (DTuple.to_fun (post PRE)))
  (PRE : pre): wlpA i (post PRE).
Proof.
  constructor; case F as [F].
  apply F, C.
Qed.

Ltac by_wlp_ dmatch :=
  refine (by_wlp_lem _ _);
  [ build_wlp_formula_ dmatch | cbn].

Ltac by_wlp := by_wlp_ false.

Ltac decompose' H :=
  lazymatch goal with | H : ?T |- _ =>
  lazymatch T with
  | exists _, _ =>
      let H0 := fresh "H" in
      destruct H as [? H0]; decompose' H0
  | _ /\ _ =>
      let H0 := fresh "H" in
      let H1 := fresh "H" in
      destruct H as [H0 H1];
      decompose' H0;
      decompose' H1
  | True  => destruct H
  | False => destruct H
  | unit  => destruct H
  | _ = _ => subst
  | context[match ?x with _ => _ end] =>
      destruct x; decompose' H
  | _ => idtac
  end end.

(* decompose a generated wlp *)
Ltac solve_wlp :=
  lazymatch goal with
  | |- _ /\ _ =>
      split; solve_wlp
  | |- _ -> _ =>
      let H := fresh "H" in intro H; decompose' H; solve_wlp
  | |- forall _, _ =>
      let H := fresh "H" in intro H; decompose' H; solve_wlp
  | |- @ex ?A _ =>
      tryif constr_eq_strict ltac:(type of A) Prop
      then unshelve eexists; solve_wlp
      else idtac
  | _ =>
      try solve [split];
      try lazymatch goal with |- context[match ?x with _ => _ end] =>
      destruct x; solve_wlp
      end
  end.

Ltac solve_by_wlp :=
  by_wlp_ false;
  solve_wlp;
  eauto.

(* Program simplification *)

Section SimplCont.
  Inductive k_t (A B : DTuple.p) :=
    mk_k (C : DTuple.p)
         (f : DTuple.t A -> DTuple.t C)
         (k : DTuple.arrow C (fun _ => instr B)).
  Global Arguments mk_k [_ _].

  Definition k_pull_f [A B C] (f : DTuple.t A -> DTuple.t B) : k_t B C -> k_t A C :=
    fun '(mk_k _ f' k) =>
    mk_k _ (fun x => f' (f x)) k.

  Definition k_fk [A B] (k : k_t A B) (x : DTuple.t A) : instr B :=
    let '(mk_k _ f k) := k in
    DTuple.to_fun k (f x).
  Global Arguments k_fk [_ _] !k/.

  Definition k_apply [A B] (i : instr A) (k : k_t A B) : instr B :=
    Bind i (DTuple.of_fun (k_fk k)).
  Global Arguments k_apply [_ _] i !k/.

  Local Add Parametric Morphism A B : (@k_apply A B)
    with signature (@eqv A) ==> (@eq (k_t A B)) ==> (@eqv B)
    as k_apply_morh.
  Proof.
    intros i0 i1 E k; unfold k_apply; rewrite E; reflexivity.
  Qed.

  Inductive simpl_cont [A B] (i : instr A) (k : k_t A B) (r : instr B) : Prop :=
    simpl_contI (E : eqv r (k_apply i k)).

  Definition k_None {A : DTuple.p} : k_t A A :=
    mk_k A (fun x => x) (DTuple.of_fun (@Ret A)).

  Lemma eqv_by_simpl_cont [A i0 i1]
    (S : @simpl_cont A A i0 k_None i1):
    eqv i0 i1.
  Proof.
    case S as [->].
    intro; cbn.
    apply (Spec.wp_morph (wlp_monotone _)).
    intro; rewrite !DTuple.to_of_fun; reflexivity.
  Qed.

  Lemma simpl_cont_morph [A B i0 i1] k
    (E : eqv i0 i1):
    @simpl_cont A B i0 k (k_apply i1 k).
  Proof.
    constructor.
    rewrite E.
    reflexivity.
  Qed.

  Lemma simpl_cont_def [A B] i k:
    @simpl_cont A B i k (k_apply i k).
  Proof.
    constructor; reflexivity.
  Qed.

  Lemma simpl_cont_Ret [A B] x k:
    @simpl_cont A B (Ret x) k (k_fk k x).
  Proof.
    case k as []; constructor; intro; cbn.
    rewrite DTuple.to_of_fun; reflexivity.
  Qed.


  Lemma simpl_cont_Call_pre [A B post k r]
    (C : simpl_cont (Call (Spec.mk_t None (option_map (fun post => post Logic.I) post)))
          (k_pull_f (A := A) (B := DTuple.Pcons _ _) (fun x => DTuple.pair Logic.I x) k) r):
    @simpl_cont _ B (@Call A (Spec.mk_t (Some True) post)) k r.
  Proof.
    constructor. etransitivity. apply C.
    intro; unfold k_pull_f, k_apply, k_fk; case k as []; cbn.
    apply Morphisms_Prop.ex_iff_morphism; intros [].
    case post; cbn; reflexivity.
  Qed.

  Lemma simpl_cont_Call_post [A B pre k r]
    (C : simpl_cont (Call (Spec.mk_t pre None)) k r):
    @simpl_cont _ B
      (@Call A (Spec.mk_t pre (Some (OptProp.of_fun (fun _ => DTuple.of_fun (fun _ => True)))))) k r.
  Proof.
    constructor. etransitivity. apply C.
    intro; unfold k_apply, k_fk; case k as []; cbn.
    apply Morphisms_Prop.ex_iff_morphism;  intro.
    apply Morphisms_Prop.all_iff_morphism; intro.
    rewrite OptProp.to_of_fun, !DTuple.to_of_fun.
    reflexivity.
  Qed.

  Definition k_pull_f_Call [A A' B] (s : Spec.t A) (f : DTuple.t A' -> DTuple.t A)
    (k : k_t (Call_ret (Spec.pre_p s) A) B) :
    k_t (Call_ret (Spec.pre_p s) A') B.
  Proof.
    refine (k_pull_f _ k).
    cbn.
    intros [PRE x]%of_Call_ret.
    exact (to_Call_ret (PRE, f x)).
  Defined.
  Global Arguments k_pull_f_Call _ _ _ _ _ _/.

  Lemma simpl_cont_Call [A A' B s k rf rg r]
    (Ru : DTuple.iso_p A A' rf rg)
    (C : simpl_cont (@Call A' (Spec.pull_f rg s)) (k_pull_f_Call s rg k) r):
    @simpl_cont _ B (@Call A s) k r.
  Proof.
    constructor. etransitivity. apply C.
    destruct k, Ru as [[R0 R1]]; cbn.
    intro; unfold k_pull_f_Call, k_apply, k_fk; cbn.
    apply Morphisms_Prop.ex_iff_morphism; intro PRE.
    setoid_rewrite Spec.pull_f_post.
    split; intros H x;
    [ generalize (H (rf x)) | generalize (H (rg x)) ];
    clear H; rewrite !DTuple.to_of_fun, (proj1 (iso_Call_ret _ _)), ?R0, ?R1;
    exact (fun H => H).
  Qed.

  Lemma simpl_cont_Bind [A A' B C f0 f1 g0 g1 k rf rg]
    (Eg : DTuple.arrow A (fun x =>
            @simpl_cont B C (DTuple.to_fun g0 x) k (DTuple.to_fun g1 x)))
    (Ru : DTuple.iso_p A A' rf rg)
    (Ef : @simpl_cont A C f0 (mk_k A' rf (DTuple.of_fun (fun x => DTuple.to_fun g1 (rg x)))) f1):
    @simpl_cont B C (Bind f0 g0) k f1.
  Proof.
    constructor.
    etransitivity. apply Ef.
    cbn [k_apply k_fk].
    etransitivity. apply Bind_morph. reflexivity.
    - intro x. etransitivity.
      + rewrite !DTuple.to_of_fun.
        case Ru as [[->]].
        apply (DTuple.to_fun Eg).
      + apply R_refl. reflexivity.
        symmetry. exact (DTuple.to_of_fun _ x).
    - clear.
      case k as [].
      symmetry; apply Bind_assoc.
  Qed.

  (* TODO? directly use an eqv morphism lemma *)
  Lemma simpl_cont_Loop [A B C D Inv ini_x ini_y f rf k]
    (F : forall x : A, DTuple.arrow (C (inl x)) (fun y =>
        simpl_cont (DTuple.to_fun (f x) y) k_None (DTuple.to_fun (rf x) y))):
    @simpl_cont _ D (@Loop A B C Inv ini_x ini_y f) k (k_apply (Loop Inv ini_x ini_y rf) k).
  Proof.
    constructor; apply k_apply_morh. 2:reflexivity.
    apply Loop_morph; intros; symmetry.
    apply eqv_by_simpl_cont, (DTuple.to_fun (F x) y).
  Qed.

  Lemma simpl_cont_branch [A B C i r f k]
    (S : simpl_cont i (mk_k C f (DTuple.of_fun (fun x => Ret x))) r):
    @simpl_cont A B i (mk_k C f k) (Bind r k).
  Proof.
    constructor.
    case S; cbn [k_apply k_fk]; intros ->.
    rewrite Bind_assoc.
    apply Bind_morph; [reflexivity|intro].
    rewrite !DTuple.to_of_fun.
    intro; reflexivity.
  Qed.
End SimplCont.

Ltac build_simpl_cont :=
  cbn;
  lazymatch goal with
  | |- simpl_cont (Ret _) _ _ =>
      refine (simpl_cont_Ret _ _)
  | |- simpl_cont (Bind _ _) _ _ =>
      refine (simpl_cont_Bind _ _ _);
      [ cbn; repeat intro; build_simpl_cont
      | DTuple.build_iso_p_remove_unit
      | build_simpl_cont ]
  | |- @simpl_cont _ ?B (@Call ?A ?s) ?k _ =>
      refine (@simpl_cont_Call A _ B s k _ _ _ _ _);
      [ DTuple.build_iso_p_remove_unit |
      cbn;
      try lazymatch goal with |- @simpl_cont _ ?B (@Call ?A ?s) ?k _ =>
      refine (@simpl_cont_Call_pre A B _ k _ _);
      cbn
      end;
      try lazymatch goal with |- @simpl_cont _ ?B (@Call ?A (Spec.mk_t ?pre _)) ?k _ =>
      refine (@simpl_cont_Call_post A B pre k _ _);
      cbn
      end;
      refine (simpl_cont_def _ _) ]
  | |- simpl_cont (Assert _) _ _ =>
      refine (simpl_cont_def _ _)
  | |- simpl_cont (Oracle _) _ _ =>
      refine (simpl_cont_def _ _)
  | |- simpl_cont (Loop _ _ _ _) _ _ =>
      refine (simpl_cont_Loop _);
      [ cbn; intros; build_simpl_cont ]
  | |- simpl_cont (match ?x with _ => _ end) _ _ =>
      (tryif Tac.is_single_case x
       then idtac
       else refine (simpl_cont_branch _));
      lazymatch goal with |- simpl_cont _ _ ?r =>
      Tac.build_term r ltac:(fun tt => Tac.case_intro_keep x; shelve);
      cbn
      end;
      lazymatch goal with |- @simpl_cont ?A ?B ?i ?k ?r =>
      let i' := fresh "i" in
      case_2heads x (fun i' => @simpl_cont A B i' k) i r
      end;
      build_simpl_cont
  | |- ?g => fail "build_simpl_cont" g
  end.

Ltac simpl_prog :=
  refine (wlpA_eqv _ _);
  [ refine (eqv_by_simpl_cont _);
    build_simpl_cont
  | cbn ].

Global Opaque Ret Bind Call Assert Oracle Loop.

Module Notations.
  Export DTuple.Notations.

  Notation "f ;; g" :=
    (@Bind DTuple.Pnil _ f g)
    (at level 199, right associativity, only printing,
     format "f ;; '//' g").

  Notation "'let' x .. y <- f ; g" :=
    (Bind f (fun x => .. (fun y => g) ..))
    (at level 200, x closed binder, y closed binder, right associativity, only printing,
     format "'[' 'let'  '[' x  ..  y  <-  ']' '/  ' f ; '//' g ']'").

  Notation "'return' x" :=
    (Ret x)
    (at level 100, x at level 0, only printing).

  Notation "'call' ( 'req' : pre ) ( 'ens' x .. y : post )" :=
    (Call {| Spec.pre_p := Some pre; Spec.post_p := Some (fun x => .. (fun y => post) .. ) |})
    (at level 100, pre at level 200, x closed binder, y closed binder, post at level 200, only printing,
     format "'call'  '[hv' ( 'req'  :  pre )  '/' ( '[  ' 'ens'  '[' x  ..  y  :  ']' post ']' ) ']'").

  Notation "'call' ( 'ens' x .. y : post )" :=
    (Call {| Spec.pre_p := None; Spec.post_p := Some (fun x => .. (fun y => post) .. ) |})
    (at level 100, x closed binder, y closed binder, post at level 200, only printing,
     format "'call'  ( '[  ' 'ens'  '[' x  ..  y  :  ']' post ']' )").

  Notation "'call' ( 'ens' : post )" :=
    (Call {| Spec.pre_p := None; Spec.post_p := Some post |})
    (at level 100, post at level 200, only printing,
     format "'call'  ( '[  ' 'ens'  :  post ']' )").

  Notation "'call' ( 'req' : pre )" :=
    (Call {| Spec.pre_p := Some pre; Spec.post_p := None |})
    (at level 100, pre at level 200, only printing,
     format "'call'  ( 'req'  :  pre )").

  Notation "'call'" :=
    (Call {| Spec.pre_p := None; Spec.post_p := None |})
    (at level 100, only printing).
End Notations.
