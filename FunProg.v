From SLFun Require Import Util.
From Coq   Require Import Setoids.Setoid.

Import List.ListNotations.


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

    Definition wp_le (wp0 wp1 : wp_t) : Prop :=
      forall post : post_t, wp1 post -> wp0 post.

    Global Instance wp_PartialOrder : Rel.MakePartialOrder wp_eq wp_le.
    Proof.
      split.
      - intros ? ?; cbn; unfold Basics.flip, wp_eq, wp_le.
        repeat setoid_rewrite Rel.forall_and_comm.
        tauto.
      - Rel.by_expr (Rel.point (A -> Prop) (Basics.flip (Basics.impl))).
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

Definition le [A : DTuple.p] (p0 p1 : instr A) : Prop :=
  Spec.wp_le (wlp p0) (wlp p1).

Definition rel (e : bool) : forall [A : DTuple.p], relation (instr A) :=
  if e then eqv else le.

Global Instance instr_PartialOrder {A : DTuple.p}: Rel.MakePartialOrder (@eqv A) (@le A).
Proof.
  split.
  - intros ? ?; cbn.
    unfold Basics.flip, eqv, le.
    setoid_rewrite (Rel.partial_order_eq_iff (@Spec.wp_eq _) (@Spec.wp_le _)).
    reflexivity.
  - Rel.by_expr (Rel.pull (@wlp A) (@Spec.wp_le _)).
Qed.

Lemma eqv_iff_le [A : DTuple.p] (p0 p1 : instr A):
  eqv p0 p1 <-> le p0 p1 /\ le p1 p0.
Proof.
  unshelve eapply (Rel.partial_order_eq_iff (@eqv A) (@le A)); auto_tc.
Qed.

Inductive wlpA [A : DTuple.p] (i : instr A) (post : DTuple.arrow A (fun _ => Prop)) : Prop :=
  wlpA_I (P : wlp i (DTuple.to_fun post)).

Lemma wlpA_le [A i0 i1 post]
  (E : @le A i0 i1)
  (C : wlpA i1 post):
  wlpA i0 post.
Proof.
  constructor.
  apply E, C.
Qed.

Lemma wlpA_eqv [A i0 i1 post]
  (E : @eqv A i0 i1)
  (C : wlpA i1 post):
  wlpA i0 post.
Proof.
  eapply wlpA_le, C.
  rewrite E; reflexivity.
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

  Lemma Bind_morph_le [A B f0 f1 g0 g1]
    (Ef : le f0 f1)
    (Eg : forall x : DTuple.t A, le (DTuple.to_fun g0 x) (DTuple.to_fun g1 x)):
    le (@Bind A B f0 g0) (@Bind A B f1 g1).
  Proof.
    intro post; cbn.
    intro H.
    apply Ef.
    eapply wlp_monotone, H.
    intro; apply Eg.
  Qed.

  Lemma Bind_morph_rel [A B f0 f1 g0 g1] e
    (Ef : rel e f0 f1)
    (Eg : forall x : DTuple.t A, rel e (DTuple.to_fun g0 x) (DTuple.to_fun g1 x)):
    rel e (@Bind A B f0 g0) (@Bind A B f1 g1).
  Proof.
    destruct e; cbn in *.
    - apply eqv_iff_le; split;
      (apply Bind_morph_le; [rewrite Ef|setoid_rewrite Eg]; reflexivity).
    - apply Bind_morph_le; auto.
  Qed.

  Global Add Parametric Morphism A B : (@Bind A B)
    with signature (@eqv A) ==>
      (Rel.pull (@DTuple.to_fun A (fun _ => instr B))
        (Morphisms.pointwise_relation (DTuple.t A) (@eqv B))) ==>
      @eqv B
    as Bind_morph.
  Proof.
    intros; apply (Bind_morph_rel true); auto.
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

  Lemma Loop_morph_le [A B C Inv ini_x ini_y f0 f1]
    (E : forall (x : A) (y : DTuple.t (C (inl x))),
      le (DTuple.to_fun (f0 x) y)
          (DTuple.to_fun (f1 x) y)):
    le (@Loop A B C Inv ini_x ini_y f0)
        (@Loop A B C Inv ini_x ini_y f1).
  Proof.
    intro; cbn.
    intuition.
    apply E; auto.
  Qed.

  Lemma Loop_morph_rel [A B C Inv ini_x ini_y f0 f1] e
    (E : forall (x : A) (y : DTuple.t (C (inl x))),
      rel e (DTuple.to_fun (f0 x) y)
            (DTuple.to_fun (f1 x) y)):
    rel e (@Loop A B C Inv ini_x ini_y f0)
          (@Loop A B C Inv ini_x ini_y f1).
  Proof.
    destruct e; cbn in *.
    - apply eqv_iff_le; split;
      apply Loop_morph_le; setoid_rewrite E; reflexivity.
    - apply Loop_morph_le; auto.
  Qed.
End Instr.

(* Morphism *)

Section Morphism.
  Inductive instr_morph [A : DTuple.p] (e : bool) (HS : list Prop) (i i' : instr A) : Prop :=
    instr_morphI (H : and_list HS -> rel e i i').

  Lemma eqv_instr_morph_lem [A HS i i']
    (M : instr_morph true HS i i')
    (C : and_list HS):
    @eqv A i i'.
  Proof.
    apply M, C.
  Qed.

  Lemma le_instr_morph_lem [A HS i i']
    (M : instr_morph false HS i i')
    (C : and_list HS):
    @le A i i'.
  Proof.
    apply M, C.
  Qed.
  
  Lemma instr_morph_refl [A i] e:
    @instr_morph A e nil i i.
  Proof.
    split; cbn.
    case e; reflexivity.
  Qed.

  Lemma instr_morph_Bind [A B f0 f1 g0 g1] e:
    instr_morph e 
      [rel e f0 f1;
       DTuple.all A (fun x => rel e (DTuple.to_fun g0 x) (DTuple.to_fun g1 x))]
      (@Bind A B f0 g0)
      (@Bind A B f1 g1).
  Proof.
    split; intros (Ef & Eg & _).
    rewrite DTuple.all_iff in Eg.
    apply Bind_morph_rel; auto.
  Qed.

  Lemma instr_moprh_Loop [A B C Inv ini_x ini_y f0 f1] e:
    instr_morph e
      [forall (x : A), DTuple.all (C (inl x)) (fun y =>
         rel e (DTuple.to_fun (f0 x) y)
               (DTuple.to_fun (f1 x) y))]
      (@Loop A B C Inv ini_x ini_y f0)
      (@Loop A B C Inv ini_x ini_y f1).
  Proof.
    split; intros (E & _).
    setoid_rewrite DTuple.all_iff in E.
    apply Loop_morph_rel; auto.
  Qed.

  Lemma instr_morph_case_next [A e i H HS i']
    (C : instr_morph e HS i i'):
    @instr_morph A e (H :: HS) i i'.
  Proof.
    split. intros (_ & pf).
    apply C, pf.
  Qed.

  Lemma instr_morph_case_cons [A e i HS] i':
    @instr_morph A e (rel e i i' :: HS) i i'.
  Proof.
    split. intros (H & _); exact H.
  Qed.
End Morphism.

Ltac build_instr_morphism_match x :=
  lazymatch goal with |- @instr_morph ?A ?e ?HS ?i ?r =>
  (* A *)
  let A_d := fresh "A'" in pose (A_d := A);
  let case_x := fresh "case_x" in
  set (case_x := x) in A_d;
  let A' := eval cbv delta [A_d] in A_d in clear A_d;
  (* i *)
  Tac.generalize_match_args x case_x i ltac:(fun i' rev_args =>
  (* r *)
  let r_d := fresh "r'" in Tac.pose_build r_d (instr A') ltac:(fun _ =>
    rev_args tt; case case_x as []; intros; shelve);
  let r' := eval cbv delta [r_d] in r_d in clear r_d;
  unify r r';

  change (@instr_morph A' e HS i' r');
  enough True as _;
  [ let add_hyp _ :=
      repeat lazymatch goal with |- instr_morph _ (_ :: _) _ _ =>
        refine (instr_morph_case_next _)
      end;
      refine (instr_morph_case_cons _); shelve
    in
    rev_args tt; case case_x as []; intros;
    add_hyp tt
  | Tac.elist_end HS; split ]
  )end.

(* solves a goal [instr_morph e ?HS i ?i'] *)
Ltac build_instr_morphism :=
  lazymatch goal with |- @instr_morph ?A ?e ?HS ?i ?r =>
  Tac.intro_evar_args r ltac:(fun r' =>
  change (@instr_morph A e HS i r'));

  lazymatch i with
  | Ret  _       => exact (instr_morph_refl e)
  | Bind _ _     => refine (instr_morph_Bind e); shelve
  | Call _       => exact (instr_morph_refl e)
  | Assert _     => exact (instr_morph_refl e)
  | Oracle _     => exact (instr_morph_refl e)
  | Loop _ _ _ _ => refine (instr_moprh_Loop e); shelve
  | _ =>
      Tac.head_of i ltac:(fun i_head =>
      Tac.matched_term i_head ltac:(fun x =>
      build_instr_morphism_match x))
  end
  | |- ?g => fail "instr_morph" g
  end.

Ltac intro_instr_morphisms_goals :=
  cbn;
  let rec splits := try solve [split]; (split; [| splits]) in
  splits;
  intros.

(* on a goal [eqv i ?i'] instantiates [i'], generates some goals [eqv f ?f'] *)
Ltac eqv_instr_morph :=
  refine (eqv_instr_morph_lem _ _);
  [ build_instr_morphism
  | intro_instr_morphisms_goals ].

(* on a goal [le i ?i'] instantiates [i'], generates some goals [eqv f ?f'] *)
Ltac le_instr_morph :=
  refine (le_instr_morph_lem _ _);
  [ build_instr_morphism
  | intro_instr_morphisms_goals ].

(* WLP formula *)

Section WLP_Formula. 
  Inductive wlp_formula [A : DTuple.p] (i : instr A) (f : Spec.wp_t (DTuple.t A)) : Prop :=
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

Inductive wlp_formula_dmatch (b : bool) : Prop :=.

(* init a formula [match x with ... end] *)
Ltac init_wlp_formula_match x :=
  lazymatch goal with |- @FunProg.wlp_formula ?A ?i ?f =>
  (* A *)
  let A_d := fresh "A'" in pose (A_d := A);
  let case_x := fresh "case_x" in
  set (case_x := x) in A_d;
  let A' := eval cbv delta [A_d] in A_d in clear A_d;
  (* i *)
  Tac.generalize_match_args x case_x i ltac:(fun i' rev_args =>
  (* f *)
  let f_d := fresh "f'" in Tac.pose_build f_d (FunProg.Spec.wp_t (DTuple.t A')) ltac:(fun _ =>
    rev_args tt; case case_x as []; intros; shelve);
  let f' := eval cbv delta [f_d] in f_d in clear f_d;
  unify f f';

  change (@FunProg.wlp_formula A' i' f'); cbn beta;
  rev_args tt;
  case case_x as []; intros
  )end.

(* destructive let *)
Ltac build_wlp_formula_dlet build_f x :=
  simple refine (wlp_formula_imp _ _ _);
  [ (* f0 *) destruct x; shelve
  | (* F  *) destruct x; build_f tt
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
  | (* F  *) destruct x; build_f tt
  | (* M  *)
   cbn;
    intro (* post *);
    let f := fresh "f" in intro f;
    case_eq x;
    [ (cbn in f; conj_proj_last f; eapply proj1 in f; exact f) ..
    | cbn in f; conj_proj_last f; exact f] ].

(* solves a goal [wlp_formula i ?f] *)
Ltac build_wlp_formula :=
  let build _ := build_wlp_formula in
  cbn; clear;
  lazymatch goal with |- @wlp_formula ?A ?i ?f =>
  Tac.intro_evar_args f ltac:(fun f' =>
  change (@wlp_formula A i f'));

  lazymatch i with
  | Ret _ =>
      refine (wlp_formula_Ret _)
  | Bind _ _ =>
      refine (wlp_formula_Bind _ _);
      [ build tt | cbn; repeat intro; build tt ]
  | @Call ?A ?s =>
      exact (@wlp_formula_Call A s)
  | Assert _ =>
      refine (wlp_formula_Assert _)
  | Oracle _ =>
      refine (wlp_formula_Oracle _)
  | Loop _ _ _ _ =>
      refine (wlp_formula_Loop _);
      [ cbn; intros; build tt ]
  | _ =>
      Tac.get_flag wlp_formula_dmatch false ltac:(fun dmatch =>
      lazymatch dmatch with
      | true =>
          (* TODO? handle more general matches *)
          Tac.matched_term i ltac:(fun x =>
          tryif Tac.is_single_case x
          then build_wlp_formula_dlet   build x
          else build_wlp_formula_branch build x
          )
      | false =>
          Tac.head_of i ltac:(fun i_head =>
          Tac.matched_term i_head ltac:(fun x =>
          init_wlp_formula_match x;
          build tt
          ))
      end)
  end
  | |- ?g => fail "build_wlp_formula:1" g
  end.

Local Lemma by_wlp_lem [A] [i : instr A] [post f]
  (F : wlp_formula i f)
  (C : f (DTuple.to_fun post)):
  wlpA i post.
Proof.
  constructor; case F as [F].
  apply F, C.
Qed.

Ltac under_PRE f :=
  let PRE := fresh "PRE" in
  intro PRE;
  f tt;
  revert PRE.

Ltac by_wlp :=
  under_PRE ltac:(fun _ =>
  refine (by_wlp_lem _ _);
  [ build_wlp_formula | cbn]).

Ltac decompose_hyps :=
  subst;
  try (lazymatch goal with
  | x : unit     |- _ => destruct x
  | x : prod _ _ |- _ => destruct x as (?, ?)
  | H : ex     _ |- _ => destruct H as [? ?]
  | H : and  _ _ |- _ => destruct H as [? ?]
  | H : True     |- _ => destruct H
  | H : False    |- _ => destruct H
  | H : context[match ?x with _ => _ end] |- _ =>
      destruct x
  end;
  decompose_hyps).

(* decompose a generated wlp *)
Ltac solve_wlp :=
  cbn;
  lazymatch goal with
  | |- _ /\ _ =>
      split; solve_wlp
  | |- _ -> _ =>
      let H := fresh "H" in
      intro H; decompose_hyps; solve_wlp
  | |- forall _, _ =>
      let x := fresh "x" in
      intro x; decompose_hyps; solve_wlp
  | |- @ex ?A _ =>
      tryif constr_eq_strict ltac:(type of A) Prop
      then unshelve eexists; solve_wlp
      else idtac
  | _ =>
      try solve [split];
      try lazymatch goal with |- context[match ?x with _ => _ end] =>
      destruct x; decompose_hyps; solve_wlp
      end
  end.

Ltac solve_by_wlp :=
  by_wlp;
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

  Lemma k_apply_morph [A B i0 i1 k]
    (E : le i0 i1):
    le (@k_apply A B i0 k)
       (@k_apply A B i1 k).
  Proof.
    unfold k_apply.
    apply Bind_morph_le; [exact E|reflexivity].
  Qed.

  (* The simplifications are expected to be complete (i.e. to not change a
     provable program into an unprovable one). Using [le] instead of [eqv] avoid using proof
     irrelevance when solving trivial call preconditions. *)
  Inductive simpl_cont [A B] (i : instr A) (k : k_t A B) (r : instr B) : Prop :=
    simpl_contI (E : le (k_apply i k) r).

  Lemma simpl_contI_eq [A B] i k r
    (E : eqv (@k_apply A B i k) r):
    simpl_cont i k r.
  Proof.
    constructor; rewrite E; reflexivity.
  Qed.

  Definition k_None {A : DTuple.p} : k_t A A :=
    mk_k A (fun x => x) (DTuple.of_fun (@Ret A)).

  Lemma le_by_simpl_cont [A i0 i1]
    (S : @simpl_cont A A i0 k_None i1):
    le i0 i1.
  Proof.
    etransitivity; [|apply S].
    intro; cbn.
    apply (Spec.wp_morph (wlp_monotone _)).
    intro; rewrite !DTuple.to_of_fun; reflexivity.
  Qed.

  Lemma simpl_cont_morph [A B i0 i1] k
    (E : le i0 i1):
    @simpl_cont A B i0 k (k_apply i1 k).
  Proof.
    constructor.
    apply k_apply_morph, E.
  Qed.

  Lemma simpl_cont_def [A B] i k:
    @simpl_cont A B i k (k_apply i k).
  Proof.
    apply simpl_contI_eq; reflexivity.
  Qed.

  Lemma simpl_cont_Ret [A B] x k:
    @simpl_cont A B (Ret x) k (k_fk k x).
  Proof.
    apply simpl_contI_eq; case k as []; intro; cbn.
    rewrite DTuple.to_of_fun; reflexivity.
  Qed.


  Lemma simpl_cont_Call_triv [B] k:
    @simpl_cont DTuple.Pnil B (@Call DTuple.Pnil {| Spec.pre_p := None; Spec.post_p := None |})
      k (k_fk k tt).
  Proof.
    apply simpl_contI_eq; case k as []; intro; cbn.
    split.
    - intros (_ & H).
      apply (H tt). split.
    - intro H; unshelve eexists. split.
      intros [] _; exact H.
  Qed.

  Lemma simpl_cont_Call_pre [A B] [pre : Prop] [post k r]
    (T : pre)
    (C : simpl_cont (Call (Spec.mk_t None (option_map (fun post => post T) post)))
          (k_pull_f (A := A) (B := DTuple.Pcons _ _) (fun x => DTuple.pair T x) k) r):
    @simpl_cont _ B (@Call A (Spec.mk_t (Some pre) post)) k r.
  Proof.
    constructor. etransitivity; [|apply C].
    intro; unfold k_pull_f, k_apply, k_fk; case k as []; cbn.
    intros [[] H].
    exists T; intros res POST.
    refine (H res _); revert POST;
    case post; cbn; auto.
  Qed.

  Lemma simpl_cont_Call_post [A B pre k r]
    (C : simpl_cont (Call (Spec.mk_t pre None)) k r):
    @simpl_cont _ B
      (@Call A (Spec.mk_t pre (Some (OptProp.of_fun (fun _ => DTuple.of_fun (fun _ => True)))))) k r.
  Proof.
    constructor. etransitivity; [apply eqv_iff_le|apply C].
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
    constructor. etransitivity; [apply eqv_iff_le|apply C].
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
    etransitivity; [|apply Ef].
    cbn [k_apply k_fk].
    etransitivity; cycle 1. apply Bind_morph_le. reflexivity.
    - intro x. etransitivity; cycle 1.
      + rewrite !DTuple.to_of_fun.
        case Ru as [[->]].
        apply (DTuple.to_fun Eg).
      + apply R_refl. reflexivity.
        exact (DTuple.to_of_fun _ x).
    - clear.
      case k as [].
      apply eqv_iff_le.
      symmetry; apply Bind_assoc.
  Qed.

  Lemma simpl_cont_branch [A B C i r f k]
    (S : simpl_cont i (mk_k C f (DTuple.of_fun (fun x => Ret x))) r):
    @simpl_cont A B i (mk_k C f k) (Bind r k).
  Proof.
    constructor.
    case S; cbn [k_apply k_fk]; intro H.
    etransitivity; [apply eqv_iff_le|apply Bind_morph_le; [exact H|reflexivity]].
    rewrite Bind_assoc.
    apply Bind_morph; [reflexivity|intro].
    rewrite !DTuple.to_of_fun.
    intro; reflexivity.
  Qed.
End SimplCont.

Ltac init_simpl_cont_match x :=
  lazymatch goal with |- (@FunProg.simpl_cont ?A ?B ?i ?k ?r) =>
  (* A, B, k *)
  let i_v := fresh "i" in
  let F_d := fresh "F'" in
  pose (F_d := fun i_v => @FunProg.simpl_cont A B i_v k);
  let case_x := fresh "case_x" in
  set (case_x := x) in F_d;
  let F' := eval cbv delta [F_d] in F_d in clear F_d;
  (* i *)
  Tac.generalize_match_args x case_x i ltac:(fun i' rev_args =>
  (* r *)
  let r_d := fresh "r'" in Tac.pose_build r_d (FunProg.instr B) ltac:(fun _ =>
    rev_args tt; case case_x as []; intros; shelve);
  let r' := eval cbv delta [r_d] in r_d in clear r_d;
  unify r r';

  change (F' i' r'); cbn beta;
  rev_args tt;
  case case_x as []; intros
  )end.

(* solves a goal [simpl_cont i k ?r] *)
Ltac build_simpl_cont :=
  cbn;
  lazymatch goal with | |- @simpl_cont ?A ?B ?i ?k ?r =>
  Tac.intro_evar_args r ltac:(fun r' =>
  change (@simpl_cont A B i k r'));

  lazymatch i with
  | Ret _ =>
      refine (simpl_cont_Ret _ _)
  | Bind _ _ =>
      refine (simpl_cont_Bind _ _ _);
      [ cbn; repeat intro; build_simpl_cont
      | DTuple.build_iso_p_remove_unit
      | build_simpl_cont ]
  | @Call ?A ?s =>
      refine (@simpl_cont_Call A _ B s k _ _ _ _ _);
      [ DTuple.build_iso_p_remove_unit |
      cbn;
      try lazymatch goal with |- @simpl_cont _ ?B (@Call ?A ?s) ?k _ =>
        simple refine (@simpl_cont_Call_pre A B _ _ k _ _ _);
        [ (* T *) solve [ split ]
        | cbn ]
      end;
      try lazymatch goal with |- @simpl_cont _ ?B (@Call ?A (Spec.mk_t ?pre _)) ?k _ =>
        refine (@simpl_cont_Call_post A B pre k _ _);
        cbn
      end;
      try refine (simpl_cont_Call_triv _);
      refine (simpl_cont_def _ _) ]
  | _ =>
      Tac.head_of i ltac:(fun i_head =>
      lazymatch i_head with
      | (match ?x with _ => _ end) =>
          (tryif Tac.is_single_case x
           then idtac
           else refine (simpl_cont_branch _));
          init_simpl_cont_match x;
          build_simpl_cont
      | _ =>
          refine (simpl_cont_morph _ _);
          le_instr_morph;
          refine (le_by_simpl_cont _);
          build_simpl_cont
      end)
  end
  | |- ?g => fail "build_simpl_cont" g
  end.

(* NOTE: it can be useful to call it twice, since the simplification of Ret can
   allow the simplification of some Call preconditions. *)
Ltac simpl_prog :=
  under_PRE ltac:(fun _ =>
  refine (wlpA_le _ _);
  [ refine (le_by_simpl_cont _);
    build_simpl_cont
  | cbn ]).

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
