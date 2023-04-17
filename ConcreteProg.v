Require Export SLFun.Values.

Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.


Module Spec. Section Spec.
  Local Set Implicit Arguments.
  Variable A : Type.

  Definition wp_t := forall (post : A -> mem -> Prop) (m0 : mem), Prop.

  Definition monotone (wp : wp_t) : Prop :=
    forall (post0 post1 : A -> mem -> Prop) (LE : forall x m, post0 x m -> post1 x m) m,
    wp post0 m -> wp post1 m.
  
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
  match o with
  | Some x => f x
  | None   => unit
  end.

Definition impl_context := forall f : fid, opt_type f_impl (SG f).

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

Definition context_oracle_free (c : impl_context) : Prop :=
  forall (f : fid),
  match SG f as sg return opt_type f_impl sg -> Prop with
  | Some sig => fun imp => forall x : f_arg_t sig, oracle_free (imp x)
  | None     => fun _   => True
  end (c f).

Definition f_spec (sg : f_sig) : Type := f_arg_t sg -> Spec.t (f_ret_t sg) -> Prop.

Definition spec_context :=
  forall f : fid, opt_type f_spec (SG f).

Section WLP.
  Variable G : spec_context.
  
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
  Variables (C : impl_context) (S : spec_context).

  Definition context_match_spec : Prop :=
    forall f,
    match SG f as sg return
      opt_type f_impl sg -> opt_type f_spec sg -> Prop
    with
    | Some sg => @f_match_spec S sg
    | None    => fun _  _  => True
    end (C f) (S f).

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

End Concrete.
Global Arguments impl_context : clear implicits.
Global Arguments spec_context : clear implicits.

