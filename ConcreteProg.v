From SLFun Require Export Values.
From SLFun Require Import Util.
From Coq   Require Import Relations.Relations Setoids.Setoid.


(* sig ghost *)
Inductive sigG (A : Type) (P : A -> Type) : Type :=
  existG (x : A) (y : P x).
Global Arguments existG [_] P.

Definition projG1 [A P] (x : sigG A P) : A :=
  let '(existG _ x _) := x in x.
Definition projG2 [A P] (x : sigG A P) : P (projG1 x) :=
  let '(existG _ _ y) := x in y.
Definition split_sigG [A P B] (f : forall (x : A) (y : P x), B) (x : sigG A P) : B :=
  f (projG1 x) (projG2 x).


Module Spec. Section Spec.
  Local Set Implicit Arguments.
  Variable A : Type.

  Definition wp_t := forall (post : A -> mem -> Prop) (m0 : mem), Prop.

  Definition monotone (wp : wp_t) : Prop :=
    forall (post0 post1 : A -> mem -> Prop) (LE : forall x m, post0 x m -> post1 x m) m,
    wp post0 m -> wp post1 m.

  Definition wp_le (wp0 wp1 : wp_t) : Prop :=
    forall post m0, wp1 post m0 -> wp0 post m0.

  Global Instance wp_le_PreOrder : PreOrder wp_le.
  Proof.
    Rel.by_expr (Rel.point (A -> mem -> Prop) (Rel.point mem (Basics.flip (Basics.impl)))).
  Qed.
  
  Record t := mk {
    pre  : mem -> Prop;
    post : mem -> A -> mem -> Prop;
  }.

  Definition le (a b : t) :=
    forall m0 : mem,
    pre b m0 -> (pre a m0 /\
    forall (r : A) (m1 : mem),
    post a m0 r m1 -> post b m0 r m1).

  Global Instance le_PreOrder : PreOrder le.
  Proof.
    unfold le. split.
    - intro; auto.
    - intros a b c L0 L1 m0 PC.
      case (L1 m0) as (PB & L1'); auto.
      case (L0 m0) as (PA & L0'); auto.
  Qed.

  Definition wp_impl (wp : wp_t) (s : t) :=
    forall m0, pre s m0 -> wp (post s m0) m0.
End Spec. End Spec.

Section Concrete.
  Context [SG : sig_context].

Inductive instr : Type -> Type :=
  | Ret  [A] (x : A) : instr A
  | Bind [A B] (f : instr A) (g : A -> instr B) : instr B
  | Call [sg : f_sig] (f : fid) (SIG : SG f = Some sg) (x : f_arg_t sg) : instr (f_ret_t sg)
  | Oracle (A : Type) : instr A
  | Assert (P : mem -> Prop) : instr unit
  (* Memory *)
  | Read (p : ptr) : instr memdata
  | Write (p : ptr) (x : memdata) : instr unit.

Definition f_impl (sig : f_sig) := f_arg_t sig -> instr (f_ret_t sig).

Definition opt_type [A] (f : A -> Type) (o : option A) : Type :=
  OptTy.t (option_map f o).

Definition impl_context' (SG' : sig_context) := forall f : fid, opt_type f_impl (SG' f).

Definition impl_context := impl_context' SG.

(* Small step semantics *)

Section Semantics.
  Variable G : impl_context.

  Definition state A := (mem * instr A)%type.

  Definition get_fun_body [sg] (f : fid) (SIG : SG f = Some sg) : f_arg_t sg -> instr (f_ret_t sg).
  Proof.
    specialize (G f).
    rewrite SIG in G.
    exact G.
  Defined.

  Inductive step : forall [A], state A -> state A -> Prop :=
    | step_bind_l m m' [A B] (f f' : instr A) (g : A -> instr B)
        (STEP_l : step (m, f) (m', f')):
        step (m, Bind f g) (m', Bind f' g)
    | step_bind_r m [A B] (x : A) (g : A -> instr B):
        step (m, Bind (Ret x) g) (m, g x)
    | step_call m sg f SIG x:
        step (m, @Call sg f SIG x) (m, get_fun_body f SIG x)
    | step_assert m (P : mem -> Prop)
        (ASSERT : P m):
        step (m, Assert P) (m, Ret tt)
    | step_read m p
        (NNULL : p <> NULL):
        step (m, Read p) (m, Ret (Mem.read m p))
    | step_write m p x
        (NNULL : p <> NULL):
        step (m, Write p x) (Mem.write m p x, Ret tt).

  Definition steps [A] : state A -> state A -> Prop :=
    clos_refl_trans_n1 _ (@step A).

  Definition okstate [A] (s : state A) :=
    (exists x, snd s = Ret x) \/ (exists s', step s s').
End Semantics.

(* Specification and proof *)

Fixpoint oracle_free [A] (i : instr A) : Prop :=
  match i with
  | Oracle _ => False
  | Bind f g => oracle_free f /\ forall x, oracle_free (g x)
  | _        => True
  end.

Definition context_oracle_free' SG' (c : impl_context' SG') : Prop :=
  forall (f : fid),
  match SG' f as sg return opt_type f_impl sg -> Prop with
  | Some sig => fun imp => forall x : f_arg_t sig, oracle_free (imp x)
  | None     => fun _   => True
  end (c f).

Definition context_oracle_free : impl_context -> Prop :=
  context_oracle_free' SG.

Definition f_spec (sg : f_sig) : Type := f_arg_t sg -> Spec.t (f_ret_t sg) -> Prop.

Definition spec_context SG :=
  forall f : fid, opt_type f_spec (SG f).

Section WLP.
  Variable G : spec_context SG.
  
  Definition fun_has_spec [sg] (f : fid) (SIG : SG f = Some sg) : f_spec sg.
  Proof.
    specialize (G f).
    rewrite SIG in G.
    exact G.
  Defined.

  Fixpoint wlp [A] (i : instr A) {struct i} : Spec.wp_t A :=
    match i with
    | Ret x => fun post =>
        post x
    | Bind f g => fun post =>
        wlp f (fun y => wlp (g y) post)
    | @Call sg f SIG x => fun post m =>
        exists s, fun_has_spec f SIG x s /\
          Spec.pre s m /\
          forall r m', Spec.post s m r m' -> post r m'
    | Oracle A => fun post m =>
        exists x : A, post x m
    | Assert P => fun post m =>
        P m /\ post tt m
    | Read p => fun post m =>
        p <> NULL /\ post (Mem.read m p) m
    | Write p x => fun post m =>
        p <> NULL /\ post tt (Mem.write m p x)
    end.

  Lemma wlp_monotone [A] (i : instr A):
    Spec.monotone (wlp i).
  Proof.
    induction i using instr_ind; do 4 intro; simpl;
    try solve [apply LE | intuition eauto].
    - (* Bind *)
      apply IHi.
      do 2 intro; apply H, LE.
    - (* Call *)
      intros (? & ? & ? & IMP).
      eexists; do 2 (esplit; [eassumption|]).
      intros; apply LE, IMP; assumption.
    - (* Oracle *)
      intros (? & P); eauto.
  Qed.

  Definition f_match_spec [sg : f_sig] (fi : f_impl sg) (fs : f_spec sg) : Prop :=
    forall x s, fs x s -> Spec.wp_impl (wlp (fi x)) s.
End WLP.

Section WLP_Correct.
  Variables (C : impl_context) (S : spec_context SG).

  Definition context_match_spec' SG' (C' : impl_context' SG') (S' : spec_context SG') : Prop :=
    forall f,
    match SG' f as sg return
      opt_type f_impl sg -> opt_type f_spec sg -> Prop
    with
    | Some sg => @f_match_spec S sg
    | None    => fun _  _  => True
    end (C' f) (S' f).

  Definition context_match_spec : Prop := context_match_spec' SG C S.

  Hypothesis MATCH : context_match_spec.
  
  Lemma elim_MATCH sg f (SIG : SG f = Some sg) s x
    (FS : fun_has_spec S f SIG x s):
    Spec.wp_impl (wlp S (get_fun_body C f SIG x)) s.
  Proof.
    specialize (MATCH f); unfold get_fun_body, fun_has_spec in *.
    set (CF := C f) in *; set (SF := S f) in *; clearbody CF SF.
    rewrite <- (eq_sym_involutive SIG) in *.
    destruct (eq_sym SIG); simpl in *.
    apply MATCH; assumption.
  Qed.

  Lemma wlp_preserved A s s' (post : A -> mem -> Prop):
    step C s s' ->
    wlp S (snd s) post (fst s) -> wlp S (snd s') post (fst s').
  Proof.
    induction 1; simpl; try solve [intuition auto].
    - (* Call *)
      intros (s & SF & PRE & POST).
      eapply elim_MATCH in SF; eauto.
      eapply wlp_monotone, SF; eauto.
  Qed.

  Lemma wlp_step A m i (post : A -> mem -> Prop)
    (WLP : wlp S i post m)
    (OFREE : oracle_free i):
    okstate C (m, i).
  Proof.
    unfold okstate; induction i; simpl in *.
    1:left; eauto. (* Ret *)
    all:right; try solve [case OFREE | intuition eauto using step].
    - (* Bind *)
      ecase IHi as [(? & ->)|((?,?) & STEP)]. apply WLP. apply OFREE.
      all:eauto using step.
  Qed.

  Hypothesis COFREE : context_oracle_free C.

  Lemma elim_COFREE sg f (SIG : SG f = Some sg) x:
    oracle_free (get_fun_body C f SIG x).
  Proof.
    specialize (COFREE f); unfold get_fun_body.
    set (CF := C  f) in *; clearbody CF.
    rewrite <- (eq_sym_involutive SIG).
    destruct (eq_sym SIG); simpl.
    apply COFREE.
  Qed.

  Lemma ofree_preserved A s s'
    (OFREE : @oracle_free A (snd s)):
    step C s s' -> oracle_free (snd s').
  Proof.
    induction 1; simpl in *; intuition auto.
    - (* Call *)
      apply elim_COFREE.
  Qed.

  Lemma wlp_stars_okstate A s s' post
    (OFREE : @oracle_free A (snd s))
    (WLP : wlp S (snd s) post (fst s))
    (STEPS : steps C s s'):
    okstate C s'.
  Proof.
    assert (H : wlp S (snd s') post (fst s') /\ oracle_free (snd s')). {
      induction STEPS; auto.
      destruct IHSTEPS.
      eauto using wlp_preserved, ofree_preserved.
    }
    case s' as (m, i).
    eapply wlp_step; apply H. 
  Qed.

  Lemma func_okstate sg f s x m s'
    (SIG : SG f = Some sg)
    (FS : fun_has_spec S f SIG x s)
    (PRE : Spec.pre s m)
    (STEPS : steps C (m, get_fun_body C f SIG x) s'):
    okstate C s'.
  Proof.
    eapply elim_MATCH in PRE; try eassumption.
    eapply wlp_stars_okstate, STEPS.
    - apply elim_COFREE.
    - exact PRE.
  Qed.
End WLP_Correct.

Section Extraction.
  Inductive k_opt (A : Type) : forall B : Type, Type :=
    | KNone : k_opt A A
    | KDrop : k_opt A unit
    | KFun [B] (f : A -> B) : k_opt A B.
  Global Arguments KNone {_}.
  Global Arguments KDrop {_}.
  Global Arguments KFun [_ _].

  Definition k_apply [A B] (i : instr A) (k : k_opt A B) : instr B :=
    match k with
    | KNone  => i
    | KDrop  => Bind i (fun _ => Ret tt)
    | KFun f => Bind i (fun x => Ret (f x))
    end.

  Lemma k_apply_morph [A B] (i0 i1 : instr A) (k : k_opt A B) SPEC
    (LE : Spec.wp_le (wlp SPEC i0) (wlp SPEC i1)):
    Spec.wp_le (wlp SPEC (k_apply i0 k)) (wlp SPEC (k_apply i1 k)).
  Proof.
    destruct k; cbn; do 2 intro; apply LE.
  Qed.

  Definition k_apply_Ret [A B] (x : A) (k : k_opt A B) : instr B :=
    match k with
    | KNone  => Ret x
    | KDrop  => Ret tt
    | KFun f => Ret (f x)
    end.

  Lemma k_apply_Ret_le [A B] x k SPEC:
    Spec.wp_le (wlp SPEC (@k_apply_Ret A B x k)) (wlp SPEC (k_apply (Ret x) k)).
  Proof.
    destruct k; intro; cbn; auto.
  Qed.

  Inductive extract_cont [A B] (i : instr A) (k : k_opt A B) (r : instr B) : Prop :=
    extract_contI (E : forall SPEC, Spec.wp_le (wlp SPEC r) (wlp SPEC (k_apply i k))).

  Record extract [A] (i0 i1 : instr A) := {
    extract_wlp : forall SPEC, Spec.wp_le (wlp SPEC i1) (wlp SPEC i0);
    extract_oracle_free : oracle_free i1;
  }.

  Lemma extract_by_cont [A i0 i1 i2]
    (E : @extract_cont A A i0 KNone i1)
    (R : i2 = i1)
    (F : oracle_free i2):
    extract i0 i2.
  Proof.
    subst i2.
    split. apply E. apply F.
  Qed.

  Lemma ERefl [A B] [i : instr A] (k : k_opt A B):
    extract_cont i k (k_apply i k).
  Proof.
    constructor. reflexivity.
  Qed.

  Inductive edroppable {A : Type}: instr A -> Prop :=
    | EDrRet  x : edroppable (Ret x)
    | EDrOracle : edroppable (Oracle A).

  Lemma EDrop [A i]
    (D : @edroppable A i):
    @extract_cont A unit i KDrop (Ret tt).
  Proof.
    constructor; intros SPEC post m0; destruct D; cbn; auto.
    intros [? ?]; auto.
  Qed.

  Lemma EDropUnit [B i k]
    (D : @edroppable unit i):
    @extract_cont unit B i k (k_apply_Ret tt k).
  Proof.
    constructor; intros SPEC post m0 W; destruct D; cbn;
    apply k_apply_Ret_le.
    - destruct x; auto.
    - eapply k_apply_morph, W; intros ? ? [[] H]; exact H.
  Qed.

  Lemma EDropAssert [B P] k:
    @extract_cont unit B (Assert P) k (k_apply_Ret tt k).
  Proof.
    constructor; intros SPEC post m0; cbn.
    destruct k; cbn; tauto.
  Qed.

  Lemma ECompRet [A B] x f:
    @extract_cont A B (Ret x) (KFun f) (Ret (f x)).
  Proof.
    constructor; do 3 intro; cbn. auto.
  Qed.

  Inductive ebind:
    forall [A B : Type] (g : A -> instr B) (A' : Type) (k : k_opt A A') (g' : A' -> instr B), Prop :=
    | EBind_Refl [A B]   g : @ebind A B g A KNone g
    | EBind_Drop [A B]   g : @ebind A B (fun _ => g) unit KDrop (fun _ => g)
    | EBind_SigG [A P B] g g'
        (G : forall x y, g (existG _ x y) = g' x)
        : @ebind (sigG A P) B g A (KFun (fun '(existG _ x _) => x)) g'.

  Lemma EBind [A0 A1 B C] [f0 f1 g0 g1 g2] [kg kf]
    (Eg : forall x : A0, @extract_cont B C (g0 x) kg (g1 x))
    (Eb : @ebind A0 C g1 A1 kf g2)
    (Ef : @extract_cont A0 A1 f0 kf f1):
    @extract_cont B C (Bind f0 g0) kg (Bind f1 g2).
  Proof.
    constructor.
    intros SPEC post m0; cbn.
    intro W0.
    apply Ef.
    assert (W1 : wlp SPEC (Bind f0 g1) post m0). {
      cbn; destruct kg; cbn in W0; eapply wlp_monotone, W0;
      cbn; intros x m1; apply Eg.
    }
    destruct Eb; cbn in *; try solve [apply W1].
    - (* EBind_SigG *)
      eapply wlp_monotone, W1; cbn.
      intros [x y] m1.
      rewrite G; auto.
    Qed.
End Extraction.

End Concrete.
Global Arguments impl_context : clear implicits.
Global Arguments spec_context : clear implicits.

Section ListRepresentation.
  Import Coq.Lists.List List.ListNotations.

  Definition context := {SIG : sig_context & spec_context SIG}.

  Record context_entry := {
    ce_sig  : f_sig;
    ce_spec : f_spec ce_sig;
  }.

  Definition context_has_entry (CT : context) (f : fid) (e : context_entry) :=
    {HSIG : projT1 CT f = Some (ce_sig e) | fun_has_spec (projT2 CT) f HSIG = ce_spec e}.

  Local Set Implicit Arguments.
  Record entry_impl_correct (CT : context) (e : context_entry) (r : @f_impl (projT1 CT) (ce_sig e)) : Prop := {
    ce_correct     : f_match_spec (projT2 CT) r (ce_spec e);
    ce_oracle_free : forall x : f_arg_t (ce_sig e), oracle_free (r x);
  }.
  Local Unset Implicit Arguments.

  Definition empty_context : context.
  Proof.
    exists (fun _ => None).
    exact  (fun _ => tt).
  Defined.

  Definition cons_context_entry (e : context_entry) (CT : context) : context.
  Proof.
    unshelve eexists.
    - intros [|f].
      + exact (Some (ce_sig e)).
      + exact (projT1 CT f).
    - intros [|f].
      + exact (ce_spec e).
      + exact (projT2 CT f).
  Defined.

  Definition context_of : list context_entry -> context :=
    List.fold_right cons_context_entry empty_context.

  Lemma context_of_has_entries es:
    and_list (mapi (context_has_entry (context_of es)) es).
  Proof.
    induction es.
    - constructor.
    - split.
      + unshelve eexists; reflexivity.
      + cbn.
        destruct (context_of es).
        exact IHes.
  Defined.

  Definition impl_list' SIG es :=
    Tuple.t (List.map (fun e => @f_impl SIG (ce_sig e)) es).

  Definition impl_list es := impl_list' (projT1 (context_of es)) es.

  Definition impl_of_list' [IT] es (l : Tuple.t (List.map (fun e => IT (ce_sig e)) es)):
    forall f : fid, opt_type IT (projT1 (context_of es) f).
  Proof.
    revert l; induction es as [|e es IH]; cbn.
    - constructor.
    - intros (i, is) [|f].
      + exact i.
      + exact (IH is f).
  Defined.

  Definition impl_of_list [es] (l : impl_list es) : impl_context (projT1 (context_of es))
    := impl_of_list' es l.

  Definition program_ok' SIG SPC SIG' SPC' (IMPL : @impl_context' SIG SIG') :=
    @context_match_spec' SIG SPC SIG' IMPL SPC' /\
    @context_oracle_free' SIG SIG' IMPL.

  Fixpoint impl_list_correct CT es : impl_list' (projT1 CT) es -> Prop :=
    match es with
    | nil     => fun _       => True
    | e :: es => fun '(i, l) => entry_impl_correct CT e i /\ impl_list_correct CT es l
    end.

  Lemma program_ok_of_list CT es (l : impl_list' (projT1 CT) es)
    (H : impl_list_correct CT es l):
    let CT' := context_of es in
    program_ok' (projT1 CT) (projT2 CT) (projT1 CT') (projT2 CT') (impl_of_list' es l).
  Proof.
    split; revert l H;
    (induction es; [constructor|
     intros (p, l) [H0 H1] [|f]; [|exact (IHes l H1 f)]]).
    - exact (ce_correct H0).
    - exact (ce_oracle_free H0).
  Qed.

  Definition of_entries (es : list context_entry) (p : impl_list es) : Prop :=
    let IMPL := impl_of_list p in
    context_match_spec IMPL (projT2 (context_of es)) /\
    context_oracle_free IMPL.
End ListRepresentation.


(* solves a goal [ebind g ?A' ?k ?g'] *)
Ltac build_ebind :=
  tryif refine (EBind_SigG _ _ _)
  then cbn; try reflexivity;
       match goal with |- ?g => fail "EBind_SigG" g end
  else first [exact (EBind_Drop _) | exact (EBind_Refl _)].

(* solves a goal [extract_cont i k ?r].
   The head of [i] must be a constructor of [instr].
   [ktac] is a tactic that solves [extract_cont i k ?r] for a more general form of [i],
   defined latter using [build_extract_cont_k] *)
Ltac build_extract_cont_k ktac :=
  lazymatch goal with
  |- @extract_cont ?SG ?A ?B ?i0 ?k ?i1 =>
      let i0' := eval hnf in i0 in
      change (@extract_cont SG A B i0' k i1);
      lazymatch i0' with
      | Assert _ =>
          exact (EDropAssert _)
      | Oracle _ =>
          try first [ exact (EDrop (@EDrOracle _ _))
                    | exact (EDropUnit (@EDrOracle _ _)) ];
          lazymatch goal with |- ?g => fail "drop oracle" g end
      | Ret _ =>
          first [ exact (EDrop (EDrRet _))
                | exact (EDropUnit (EDrRet _))
                | exact (ECompRet _ _)
                | exact (ERefl _) ]
      | Bind _ _ =>
          refine (EBind _ _ _);
          [ intro; ktac
          | cbn; build_ebind
          | ktac ]
      | _ =>
          exact (ERefl _)
      end
  end.

Ltac build_oracle_free_aux :=
  cbn;
  lazymatch goal with
  | |- @oracle_free ?SG ?A ?i =>
      lazymatch i with
      | (match ?x with _ => _ end) =>
          destruct x
      | _ =>
          let i' := eval hnf in i in
          change (@oracle_free SG A i')
      end
  | _ => first [intro | constructor]
  end.

(* solves a goal [oracle_free i] *)
Ltac build_oracle_free := repeat build_oracle_free_aux.

(* solves a goal [of_entries es ?prog]. *)

Local Lemma entry_impl_correct_change [CT e impl0 impl1]
  (C : entry_impl_correct CT e impl0)
  (E : impl0 = impl1):
  entry_impl_correct CT e impl1.
Proof.
  subst; assumption.
Qed.

Local Lemma intro_of_entries es [p1]
  (C : let CT := context_of es in
       { p0 : impl_list es | impl_list_correct CT es p0 })
  (E : p1 = proj1_sig C):
  of_entries es p1.
Proof.
  subst.
  apply program_ok_of_list.
  apply (proj2_sig C).
Qed.

Global Create HintDb extractDB discriminated.
Global Hint Constants Opaque : extractDB.
Global Hint Variables Opaque : extractDB.

Ltac build_of_entries :=
  lazymatch goal with |- of_entries ?es ?prog =>
  simple refine (intro_of_entries es _ _); [
    let CT := fresh "CT" in intro CT;
    (* derive hypotheses from [CP.context_has_entry] *)
    let rec pose_has_entry f es :=
      lazymatch es with
      | cons ?e ?es =>
          let H := fresh "H_f" in
          assert (context_has_entry CT f e) as H;
          [ exists eq_refl; reflexivity |];
          Util.Tac.apply_Arrow H;
          [ (* [Arrow (CP.context_has_entry CT fid e) ?H] *)
            solve [eauto 1 with extractDB nocore]
          |];
          pose_has_entry (S f) es
      | nil => idtac
      end
    in
    pose_has_entry O es;

    unshelve eexists; [cbn; Tuple.build_shape |];
    cbn -[CT];
    let rec loop := try solve [split]; (split; [|loop]) in loop;
    (refine (entry_impl_correct_change _ _);
     [ clearbody CT;
       (* [CP.entry_impl_correct CT e ?impl] *)
       solve [eauto 1 with extractDB nocore]
     | reflexivity ])
  |
    cbv; reflexivity
  ]
  end.

(* Exported tactics *)

Module Tactics.
  #[export] Hint Extern 1 (of_entries _ _) => build_of_entries : DeriveDB.
End Tactics.
