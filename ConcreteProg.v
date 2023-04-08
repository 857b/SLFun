Require Import Coq.Relations.Relations.

Require Export SLFun.Values.


Definition fid : Set := nat.

Record f_sig := mk_f_sig {
  f_arg_t : Type;
  f_ret_t : Type;
}.

Definition sig_context := fid -> option f_sig.

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
    | step_read m p:
        step (m, Read p) (m, Ret (Mem.read m p))
    | step_write m p x:
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

Record f_spec (sg : f_sig) := mk_f_spec {
  f_pre   : f_arg_t sg -> mem -> Prop;
  f_post  : f_arg_t sg -> mem -> f_ret_t sg -> mem -> Prop;
}.
Global Arguments f_pre  [_].
Global Arguments f_post [_].

Definition spec_context :=
  forall f : fid, opt_type (fun sg => f_spec sg -> Prop) (SG f).

Section WLP.
  Variable G : spec_context.
  
  Definition fun_has_spec [sg] (f : fid) (SIG : SG f = Some sg) : f_spec sg -> Prop.
  Proof.
    specialize (G f).
    rewrite SIG in G.
    exact G.
  Defined.

  Fixpoint wlp [A] (i : instr A) {struct i} : forall (post : A -> mem -> Prop) (m : mem), Prop :=
    match i with
    | Ret x => fun post =>
        post x
    | Bind f g => fun post =>
        wlp f (fun y => wlp (g y) post)
    | @Call sg f SIG x => fun post m =>
        exists s, fun_has_spec f SIG s /\
          f_pre s x m /\
          forall r m', f_post s x m r m' -> post r m'
    | Oracle A => fun post m =>
        exists x : A, post x m
    | Assert P => fun post m =>
        P m /\ post tt m
    | Read p => fun post m =>
        post (Mem.read m p) m
    | Write p x => fun post m =>
        post tt (Mem.write m p x)
    end.

  Lemma wlp_monotone [A] (i : instr A) (post0 post1 : A -> mem -> Prop) m
    (LE : forall x m, post0 x m -> post1 x m):
    wlp i post0 m -> wlp i post1 m.
  Proof.
    revert post0 post1 m LE; induction i using instr_ind; do 4 intro; simpl;
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
    forall x m, f_pre fs x m -> wlp (fi x) (f_post fs x m) m.
End WLP.

Section WLP_Correct.
  Variables (C : impl_context) (S : spec_context).

  Definition context_match_spec : Prop :=
    forall f,
    match SG f as sg return
      opt_type f_impl sg -> opt_type (fun sg => f_spec sg -> Prop) sg -> Prop
    with
    | Some sg => fun fi fs => forall s, fs s -> f_match_spec S fi s
    | None    => fun _  _  => True
    end (C f) (S f).

  Hypothesis MATCH : context_match_spec.
  
  Lemma elim_MATCH sg f (SIG : SG f = Some sg) s x m
    (FS : fun_has_spec S f SIG s)
    (PRE : f_pre s x m):
    wlp S (get_fun_body C f SIG x) (f_post s x m) m.
  Proof.
    specialize (MATCH f); unfold get_fun_body, fun_has_spec in *.
    set (CF := C f) in *; set (SF := S f) in *; clearbody CF SF.
    rewrite <- (eq_sym_involutive SIG) in *.
    destruct (eq_sym SIG); simpl in *.
    apply (MATCH s); assumption.
  Qed.

  Lemma wlp_preserved A s s' (post : A -> mem -> Prop):
    step C s s' ->
    wlp S (snd s) post (fst s) -> wlp S (snd s') post (fst s').
  Proof.
    induction 1; simpl; try solve [intuition auto].
    - (* Call *)
      intros (s & SF & PRE & POST).
      eapply elim_MATCH in SF; eauto.
      eapply wlp_monotone; eassumption.
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
    (FS : fun_has_spec S f SIG s)
    (PRE : f_pre s x m)
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

