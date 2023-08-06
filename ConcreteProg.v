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

  Definition wp_eq (wp0 wp1 : wp_t) : Prop :=
    forall post m0, wp0 post m0 <-> wp1 post m0.

  Definition wp_le (wp0 wp1 : wp_t) : Prop :=
    forall post m0, wp1 post m0 -> wp0 post m0.

  Global Instance wp_PartialOrder : Rel.MakePartialOrder wp_eq wp_le.
  Proof.
    split.
    - intros ? ?; cbn; unfold Basics.flip, wp_eq, wp_le.
      repeat setoid_rewrite Rel.forall_and_comm.
      tauto.
    - Rel.by_expr (Rel.point (A -> mem -> Prop) (Rel.point mem (Basics.flip (Basics.impl)))).
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
  | Loop [A B] (ini : A + B) (f : A -> instr (A + B)) : instr B
  | Oracle (A : Type) : instr A
    (* [Oracle] is used to introduce ghost variables. *)
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
    | step_loop_l m [A B] (f : A -> instr (A + B)) (x : A):
        step (m, @Loop A B (inl x) f) (m, Bind (f x) (fun x => Loop x f))
    | step_loop_e m [A B] (f : A -> instr (A + B)) (x : B):
        step (m, @Loop A B (inr x) f) (m, Ret x)
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

(* [Oracle] is blocking for the small-step semantics but interpreted as an existential
   quantification ("best choice") in the WLP. The WLP is thus sound only on programs that
   do not contain oracles. The erasure pass removes the oracles from a program while preserving
   its WLP. *)
Fixpoint oracle_free [A] (i : instr A) : Prop :=
  match i with
  | Oracle _ => False
  | Bind f g => oracle_free f /\ forall x, oracle_free (g x)
  | Loop _ f => forall x, oracle_free (f x)
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
    | @Loop A B x f => fun post m =>
        exists Inv : A + B -> mem -> Prop,
        Inv x m /\
        (forall (x : A) m, Inv (inl x) m -> wlp (f x) Inv m) /\
        (forall (x : B) m, Inv (inr x) m -> post x m)
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
    - (* Loop *)
      intros (Inv & ? & ? & IMP).
      exists Inv; eauto.
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
    - (* Loop loop *)
      intros (Inv & INI & PRS & ?).
      eapply wlp_monotone, PRS, INI.
      exists Inv; eauto.
    - (* Loop exit *)
      intros (Inv & INI & _ & EXIT).
      apply EXIT, INI.
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
    - (* Loop *)
      case ini; eauto using step.
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

Section Erasure.
  Inductive k_opt (A : Type) : forall B : Type, Type :=
    | KNone : k_opt A A
    | KDrop : k_opt A unit
    | KFun [B] (f : A -> B) : k_opt A B.
  Global Arguments KNone {_}.
  Global Arguments KDrop {_}.
  Global Arguments KFun [_ _].

  Definition k_f [A B] (k : k_opt A B) : A -> B :=
    match k with
    | KNone  => fun x => x
    | KDrop  => fun _ => tt
    | KFun f => f
    end.

  Definition k_apply [A B] (i : instr A) (k : k_opt A B) : instr B :=
    Bind i (fun x => Ret (k_f k x)).

  Lemma k_apply_morph [A B] (i0 i1 : instr A) (k : k_opt A B) SPEC
    (LE : Spec.wp_le (wlp SPEC i0) (wlp SPEC i1)):
    Spec.wp_le (wlp SPEC (k_apply i0 k)) (wlp SPEC (k_apply i1 k)).
  Proof.
    cbn; do 2 intro; apply LE.
  Qed.

  Definition k_apply_c [A B] (i : instr A) (k : k_opt A B) : instr B :=
    match k with
    | KNone  => i
    | KDrop  => Bind i (fun _ => Ret tt)
    | KFun f => Bind i (fun x => Ret (f x))
    end.

  Lemma k_apply_c_eq [A B] (i : instr A) (k : k_opt A B) SPEC:
    Spec.wp_eq (wlp SPEC (k_apply i k)) (wlp SPEC (k_apply_c i k)).
  Proof.
    destruct k; cbn; reflexivity.
  Qed.
  Local Opaque k_apply_c.

  Definition k_apply_Ret [A B] (x : A) (k : k_opt A B) : instr B :=
    Ret (k_f k x).


  Inductive erase_cont [A B] (i : instr A) (k : k_opt A B) (r : instr B) : Prop :=
    erase_contI (E : forall SPEC, Spec.wp_le (wlp SPEC r) (wlp SPEC (k_apply i k))).

  Record erase [A] (i0 i1 : instr A) := {
    erase_wlp : forall SPEC, Spec.wp_le (wlp SPEC i1) (wlp SPEC i0);
    erase_oracle_free : oracle_free i1;
  }.

  Lemma erase_by_cont [A i0 i1 i2]
    (E : @erase_cont A A i0 KNone i1)
    (R : i2 = i1)
    (F : oracle_free i2):
    erase i0 i2.
  Proof.
    subst i2.
    split. apply E. apply F.
  Qed.

  Lemma ERefl [A B] [i : instr A] (k : k_opt A B):
    erase_cont i k (k_apply_c i k).
  Proof.
    constructor.
    setoid_rewrite k_apply_c_eq.
    reflexivity.
  Qed.

  Inductive edroppable {A : Type}: instr A -> Prop :=
    | EDrRet  x : edroppable (Ret x)
    | EDrOracle : edroppable (Oracle A).

  Lemma EDrop [A i]
    (D : @edroppable A i):
    @erase_cont A unit i KDrop (Ret tt).
  Proof.
    constructor; intros SPEC post m0; destruct D; cbn; auto.
    intros [? ?]; auto.
  Qed.

  Lemma EDropUnit [B i k]
    (D : @edroppable unit i):
    @erase_cont unit B i k (k_apply_Ret tt k).
  Proof.
    constructor; intros SPEC post m0; destruct D; cbn.
    - case x; auto.
    - intros [[] ?]; auto.
  Qed.

  Lemma EDropAssert [B P] k:
    @erase_cont unit B (Assert P) k (k_apply_Ret tt k).
  Proof.
    constructor; intros SPEC post m0; cbn.
    destruct k; cbn; tauto.
  Qed.

  Lemma ECompRet [A B] x f:
    @erase_cont A B (Ret x) (KFun f) (Ret (f x)).
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

  Lemma ebind_spec [A B g A' k g'] (E : @ebind A B g A' k g') (x : A):
    g x = g' (k_f k x).
  Proof.
    case E as []; cbn; try reflexivity.
    - (* EBind_SigG *)
      case x as []; apply G.
  Qed.


  Lemma EBind [A0 A1 B C] [f0 f1 g0 g1 g2] [kg kf]
    (Eg : forall x : A0, @erase_cont B C (g0 x) kg (g1 x))
    (Eb : @ebind A0 C g1 A1 kf g2)
    (Ef : @erase_cont A0 A1 f0 kf f1):
    @erase_cont B C (Bind f0 g0) kg (Bind f1 g2).
  Proof.
    constructor.
    intros SPEC post m0; cbn.
    intro W0.
    apply Ef; cbn.
    eapply wlp_monotone, W0; cbn; intros x m1.
    rewrite <- (ebind_spec Eb).
    apply Eg.
  Qed.

  Section K_SUM.
    Context [A0 A1 B0 B1 : Type] (k0 : k_opt A0 B0) (k1 : k_opt A1 B1).

    Definition k_sum  : k_opt (A0 + A1) (B0 + B1) :=
      let def := @KFun (A0 + A1) (B0 + B1) (sum_map (k_f k0) (k_f k1)) in
      match k0 in k_opt _ B0, k1 in k_opt _ B1
      return k_opt _ (B0 + B1) -> k_opt _ (B0 + B1) with
      | KNone, KNone => fun _   => KNone
      | _,     _     => fun def => def
      end def.

    Lemma k_sum_f x:
      k_f k_sum x = sum_map (k_f k0) (k_f k1) x.
    Proof.
      unfold k_sum.
      case k0 as [], k1 as []; try reflexivity.
      case x; reflexivity.
    Qed.
  End K_SUM.
  Local Opaque k_sum.

  Lemma ELoop [A A' B C f0 f1 f2 x kl ke]
    (El : @ebind A _ f1 A' kl f2)
    (Ef : forall x : A, @erase_cont (A + B) (A' + C) (f0 x) (k_sum kl ke) (f1 x)):
    @erase_cont B C (@Loop A B x f0) ke (@Loop A' C (sum_map (k_f kl) (k_f ke) x) f2).
  Proof.
    constructor; intros SPEC post m0; cbn.
    intros (Inv & INI & PRS & EXIT).
    set (km := sum_map _ _).
    exists (fun y m => exists x, y = km x /\ Inv x m).
    split; [|split].
    2,3:intros y1 m1 ([x1|x1] & Y1 & INV);
        simplify_eq Y1; intros ->; clear Y1.
    - eauto.
    - rewrite <- (ebind_spec El).
      apply (Ef x1); cbn.
      eapply wlp_monotone, PRS, INV.
      setoid_rewrite k_sum_f; eauto.
    - apply EXIT, INV.
  Qed.
End Erasure.

End Concrete.
Global Arguments impl_context : clear implicits.
Global Arguments spec_context : clear implicits.

Section Context.
  Definition context := {SIG : sig_context & spec_context SIG}.

  Record context_entry := {
    ce_sig  : f_sig;
    ce_spec : f_spec ce_sig;
  }.

  Definition context_has_entry (CT : context) (f : fid) (e : context_entry) :=
    {HSIG : projT1 CT f = Some (ce_sig e) | fun_has_spec (projT2 CT) f HSIG = ce_spec e}.

  Local Set Implicit Arguments.
  Record entry_impl_correct (CT : context) (e : context_entry)
      (r : @f_impl (projT1 CT) (ce_sig e)) : Prop := {
    ce_correct     : f_match_spec (projT2 CT) r (ce_spec e);
    ce_oracle_free : forall x : f_arg_t (ce_sig e), oracle_free (r x);
  }.
  Local Unset Implicit Arguments.
End Context.

(* Compact list representation *)
Module L.
  Import Util.List ListNotations.

  (* context *)

  Definition context : Type := list context_entry.

  Definition get : context -> ConcreteProg.context.
  Proof.
    fix rec 1.
    intros [|[sg sp] c].
    - exact (existT spec_context (fun _ => None) (fun _ => tt)).
    - pose (CT := rec c).
      unshelve eexists; intros [|f].
      + exact (Some sg).
      + exact (projT1 CT f).
      + exact sp.
      + exact (projT2 CT f).
  Defined.

  (* implementations *)

  Definition impl_context_entry (SIG : sig_context) : Type :=
    {e : context_entry & @f_impl SIG (ce_sig e)}.
  
  Definition impl_context (SIG : sig_context) : Type :=
    list (impl_context_entry SIG).

  Definition impl_list (c : context) : Type :=
    impl_context (projT1 (get c)).
  
  Definition proj_impl_context [SIG : sig_context] : impl_context SIG -> context :=
    map (@projT1 _ _).

  Definition impl_match_eq (c : context) (ci : impl_list c) : Prop :=
    proj_impl_context ci = c.

  Definition get_impl' [SIG : sig_context] (ci : impl_context SIG):
    @ConcreteProg.impl_context' SIG (projT1 (get (proj_impl_context ci))).
  Proof.
    revert ci; fix rec 1.
    intros [|[[sg sp] r] ci]; cbn.
    - exact (fun _ => tt).
    - intros [|f]; cbn.
      + exact r.
      + exact (rec ci f).
  Defined.

  Definition get_impl [c : context] (ci : impl_list c) (E : impl_match_eq c ci):
    ConcreteProg.impl_context (projT1 (get c))
    := match E in _ = c' return ConcreteProg.impl_context' (projT1 (get c')) with
       eq_refl => get_impl' ci
       end.

  (* correctness *)

  Definition impl_context_correct_entry (CT : ConcreteProg.context) : Type :=
    { e : impl_context_entry (projT1 CT) | entry_impl_correct CT (projT1 e) (projT2 e) }.

  Definition impl_context_correct (CT : ConcreteProg.context) : Type :=
    list (impl_context_correct_entry CT).

  Definition proj_impl_context_correct [CT : ConcreteProg.context]
    : impl_context_correct CT -> impl_context (projT1 CT) :=
    map (@proj1_sig _ _).

  Definition program_ok' SIG SPC SIG' SPC' (IMP : @ConcreteProg.impl_context' SIG SIG') :=
    @context_match_spec' SIG SPC SIG' IMP SPC' /\
    @context_oracle_free' SIG SIG' IMP.

  Definition program_ok (c : context) (ci : impl_list c) :=
    exists E : impl_match_eq c ci,
    let SIG : sig_context                   := projT1 (get c) in
    let SPC : ConcreteProg.spec_context SIG := projT2 (get c) in
    let IMP : ConcreteProg.impl_context SIG := get_impl ci E  in
    program_ok' SIG SPC SIG SPC IMP.

  Lemma program_ok_all [c : context] [ci : impl_list c] (OK : program_ok c ci):
    forall E : impl_match_eq c ci,
    let SIG : sig_context                   := projT1 (get c) in
    let SPC : ConcreteProg.spec_context SIG := projT2 (get c) in
    let IMP : ConcreteProg.impl_context SIG := get_impl ci E  in
    program_ok' SIG SPC SIG SPC IMP.
  Proof.
    intros E0 SIG SPC; cbv zeta.
    case OK as [E1 OK].
    fold SIG SPC in OK; cbv zeta in OK.
    pose (P (c' : context) (E : proj_impl_context ci = c') :=
      program_ok' SIG SPC (projT1 (get c')) (projT2 (get c'))
        (eq_rect _ (fun c' => impl_context' (projT1 (get c'))) (get_impl' ci) _ E)).
    change (P _ E0).
    change (P _ E1) in OK.
    destruct E0, E1.
    exact OK.
  Qed.

  Lemma impl_context_correct_ok' (CT : ConcreteProg.context) (cc : impl_context_correct CT):
    let ci  := proj_impl_context_correct cc in
    let CT' := get (proj_impl_context ci)   in
    program_ok' (projT1 CT) (projT2 CT) (projT1 CT') (projT2 CT') (get_impl' ci).
  Proof.
    induction cc as [|[[[sg sp] r] C] cc IH]; cbn.
    - do 2 split.
    - split; (intros [|f]; cbn; [apply C|apply IH]).
  Qed.

  Inductive impl_match (c : context) (ci : impl_list c) : Prop :=
    impl_matchI
      (cc : impl_context_correct (get c))
      (Ec : proj_impl_context_correct cc = ci)
      (Ei : impl_match_eq c ci).

  Lemma impl_match_ok [c ci] (M : impl_match c ci): program_ok c ci.
  Proof.
    case M as [cc Ec Ei].
    exists Ei.
    specialize (impl_context_correct_ok' _ cc); cbn.
    rewrite Ec in *; clear cc Ec.
    unfold get_impl.
    case Ei; auto.
  Qed.
End L.

Definition of_entries (es : list context_entry) (p : L.impl_list es) : Prop :=
  L.program_ok es p.

(* solves a goal [ebind g ?A' ?k ?g'] *)
Ltac build_ebind :=
  tryif refine (EBind_SigG _ _ _)
  then cbn; try reflexivity;
       match goal with |- ?g => fail "EBind_SigG" g end
  else first [exact (EBind_Drop _) | exact (EBind_Refl _)].

(* on a goal [match x with ... end arg0 ... arg9 = ?rhs]
   where [arg0] ... [arg9] are local definitions,
   instantiate [?rhs] with a simplified version of the lhs. *)
Ltac simplify_match x :=
  (* tries to remove the match *)
  try (case x as []; [reflexivity]);
  (* remove the unused arguments *)
  lazymatch goal with |- @eq ?A ?lhs ?rhs =>
  let rec iter_args lhs k(* rev_args -> test_dep -> inst_used -> rev_used -> ltac *) :=
    lazymatch lhs with
    | ?lhs ?arg =>
        let used := fresh "used" in
        evar (used : bool);
        iter_args lhs ltac:(fun rev_args test_dep inst_used rev_used =>
          k ltac:(fun _ => generalize arg; clear arg; rev_args tt)
            ltac:(fun test_dep1 =>
              test_dep ltac:(fun _ =>
                let x := fresh "x" in intro x;
                test_dep1 tt;
                first [ clear x
                      | try instantiate (1 := true) in (value of used);
                        revert x ]
            ))
            ltac:(fun _ => try instantiate (1 := false) in (value of used); inst_used tt)
            ltac:(fun _ =>
              (tryif assert (used = true) as _ by reflexivity
               then generalize arg; clear arg
               else clear arg);
              rev_used tt)
        )
    | _ =>
        k ltac:(fun _ => idtac)
          ltac:(fun test_dep1 => test_dep1 tt)
          ltac:(fun _ => idtac)
          ltac:(fun _ => idtac)
    end
  in
  iter_args lhs ltac:(fun rev_args test_dep inst_used rev_used =>
    assert (Tac.display lhs) as _;
      [ rev_args tt; case x as []; test_dep ltac:(fun _ => idtac); split
      | inst_used tt ];

    let rhs' := fresh "rhs" in
    Tac.pose_build rhs' A ltac:(fun _ =>
      rev_used tt; case x as []; intros; shelve);
    cbn beta in rhs';
    unify rhs rhs';
    change (@eq A lhs rhs');
    subst rhs';

    rev_args tt; case x as []; Tac.cbn_refl
  )end.

(* solves a goal [erase_cont i k ?r].
   The head of [i] must be a constructor of [instr].
   [ktac] is a tactic that solves [erase_cont i k ?r] for a more general form of [i],
   defined latter using [build_erase_cont_k] *)
Ltac build_erase_cont_k ktac :=
  lazymatch goal with
  |- @erase_cont ?SG ?A ?B ?i0 ?k ?i1 =>
      let i0' := eval hnf in i0 in
      change (@erase_cont SG A B i0' k i1);
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
      | Loop _ _ =>
          refine (ELoop _ _);
          [ (* El *)
            tryif apply EBind_SigG
            then reflexivity
            else apply EBind_Refl
          | (* Ef *)
            intro; ktac ]
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


(* Extraction *)

(* Database for extraction.
   Called on goals:
     [Arrow (context_has_entry CT fid e) ?H]
     [entry_impl_correct CT e ?impl]
 *)
Global Create HintDb extractDB discriminated.
Global Hint Constants Opaque : extractDB.
Global Hint Variables Opaque : extractDB.

Local Definition exploit_has_entry [CT f e] R
  (H : context_has_entry CT f e)
  (A : Util.Tac.Arrow (context_has_entry CT f e) R):
  R.
Proof.
  apply A, H.
Defined.

Local Definition mk_impl_context_correct_entry CT (e : context_entry) (impl : f_impl (ce_sig e))
  (C : entry_impl_correct CT e impl):
  L.impl_context_correct_entry CT
  := exist _ (existT _ e impl) C.

Local Definition proj_impl_context_correct_red :=
  Eval cbv beta delta [L.proj_impl_context_correct List.map proj1_sig] in L.proj_impl_context_correct.
Arguments proj_impl_context_correct_red [CT] _.

Local Lemma intro_of_entries es prog ci cc
  (Ec : proj_impl_context_correct_red cc = ci)
  (Ei : L.impl_match_eq es ci)
  (Ep : prog = ci):
  of_entries es prog.
Proof.
  subst prog.
  apply L.impl_match_ok.
  exists cc; auto.
Qed.

(* solves a goal [of_entries es ?prog]. *)
Ltac build_of_entries :=
  lazymatch goal with |- of_entries ?es0 ?prog0 =>

  (* reduces and abstracts some parts of the initial goal *)
  let es0  := eval hnf in (List.force_value es0) in
  let prog := eval hnf in  prog0                 in
  change (of_entries es0 prog);
  clear;

  let rec abstract_entries es0 k(* es -> ltac *) :=
    lazymatch es0 with
    | cons ?e0 ?es0 =>
        Tac.abstract_term e0 ltac:(fun e  =>
        abstract_entries es0 ltac:(fun es =>
        k (@cons context_entry e es)))
    | nil => k (@nil context_entry)
    end
  in
  abstract_entries es0 ltac:(fun es =>
  change (of_entries es prog);

  let CT  := fresh "CT"  in
  unshelve epose (CT := _);
    [ exact context | transparent_abstract exact (L.get es) |];
  let SIG := fresh "SIG" in pose (SIG := projT1 CT);

  (* for each entry, derives an hypotheses from [context_has_entry] *)
  let rec pose_has_entry f es k(* itr -> ltac *) :=
    lazymatch es with
    | cons ?e ?es =>
        let e := eval cbv delta [e] in e in
        let t := constr:(@exploit_has_entry CT f e _ (exist _ eq_refl eq_refl)
          ltac:(
            (* [Arrow (context_has_entry CT fid e) ?H] *)
            solve_db extractDB
          )) in
        lazymatch t with exploit_has_entry ?R _ _ =>
        let t := eval hnf in t in
        let H := fresh "H_f" in
        Tac.pose_with_ty H t R;
        pose_has_entry (S f) es ltac:(fun itr =>
          k ltac:(fun g => itr g; g H))
        end
    | nil => k ltac:(fun _ => idtac)
    end
  in
  pose_has_entry O es ltac:(fun itr =>

  (* for each entry, builds an implementation proven correct in the context *)
  simple refine (intro_of_entries es prog _ _  _ _ _);
  [ (* ci *) shelve
  | (* cc *)
    change (L.impl_context_correct CT);
    itr ltac:(fun H => clearbody H); clearbody CT;
    let rec build_cc es :=
      lazymatch es with
      | cons ?e ?es =>
          refine (@cons (L.impl_context_correct_entry CT) _ _);
          [ simple refine (mk_impl_context_correct_entry CT e _ _);
            [ (* impl *) shelve
            | (* [entry_impl_correct CT e ?impl] *)
              lazymatch goal with |- entry_impl_correct _ _ ?impl =>
              let e := eval cbv delta [e] in e in
              change (entry_impl_correct CT e impl);
              Tac.eabstract ltac:(fun _ => solve_db extractDB)
              end ]
          | build_cc es ]
      | nil =>
          exact (@nil (L.impl_context_correct_entry CT))
      end
    in build_cc es
  | (* Ec *)
    itr ltac:(fun H => subst H); subst CT SIG;
    cbv beta iota zeta delta [proj_impl_context_correct_red mk_impl_context_correct_entry];
    lazymatch goal with |- ?ci = _ => exact (@eq_refl _ ci) end
  | (* Ei *)
    reflexivity
  | (* Ep *)
    lazymatch goal with |- _ = ?ci => exact (@eq_refl (L.impl_context SIG) ci) end
  ]))end.


(* Exported tactics *)

Module Tactics.
  #[export] Hint Extern 1 (of_entries _ _) => build_of_entries : DeriveDB.
End Tactics.
