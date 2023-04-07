Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relations.

Require Export SLFun.Values.

Definition fid : Set := nat.

Inductive instr : Type -> Type :=
  | Ret  [A] (x : A) : instr A
  | Bind [A B] (f : instr A) (g : A -> instr B) : instr B
  | Call [A] (R : Type) (f : fid) (x : A) : instr R
  | Oracle (A : Type) : instr A
  | Assert (P : mem -> Prop) : instr unit
  (* Memory *)
  | Read (p : ptr) : instr memdata
  | Write (p : ptr) (x : memdata) : instr unit.

Record f_impl := mk_f_impl {
  f_arg_t : Type;
  f_ret_t : Type;
  f_body  : f_arg_t -> instr f_ret_t;
}.

Definition context := fid -> option f_impl.

(* Small step semantics *)

Section Semantics.

  Variable G : context.

  Definition state A := (mem * instr A)%type.

  Inductive step : forall [A], state A -> state A -> Prop :=
    | step_bind_l m m' [A B] (f f' : instr A) (g : A -> instr B)
        (STEP_l : step (m, f) (m', f')):
        step (m, Bind f g) (m', Bind f' g)
    | step_bind_r m [A B] (x : A) (g : A -> instr B):
        step (m, Bind (Ret x) g) (m, g x)
    | step_call m f arg_t ret_t body x
        (GET_F : G f = Some (mk_f_impl arg_t ret_t body)):
        step (m, Call ret_t f x) (m, body x)
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

Definition context_oracle_free (c : context) :=
  forall f fi, c f = Some fi -> forall x, oracle_free (f_body fi x).

Record f_spec := mk_f_spec {
  fs_arg_t : Type;
  fs_ret_t : Type;
  fs_pre   : fs_arg_t -> mem -> Prop;
  fs_post  : fs_arg_t -> mem -> fs_ret_t -> mem -> Prop;
}.

Definition scontext := fid -> f_spec -> Prop.

Section WLP.
  Variable G : scontext.

  Fixpoint wlp [A] (i : instr A) {struct i} : forall (post : A -> mem -> Prop) (m : mem), Prop :=
    match i with
    | Ret x => fun post =>
        post x
    | Bind f g => fun post =>
        wlp f (fun y => wlp (g y) post)
    | @Call A R f x => fun post m =>
        exists fpre fpost, G f (mk_f_spec A R fpre fpost) /\
        fpre x m /\
        forall r m', fpost x m r m' -> post r m'
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
      intros (? & ? & ? & ? & IMP).
      do 2 eexists; do 2 (esplit; [eassumption|]).
      intros; apply LE, IMP; assumption.
    - (* Oracle *)
      intros (? & P); eauto.
  Qed.

  Inductive f_match_spec : f_impl -> f_spec -> Prop :=
    | intro_match_spec arg_t res_t (pre : arg_t -> mem -> Prop) post body
        (MATCH : forall x m, pre x m -> wlp (body x) (post x m) m):
        f_match_spec (mk_f_impl arg_t res_t body) (mk_f_spec arg_t res_t pre post).
End WLP.

Section WLP_Correct.
  Variables (C : context) (S : scontext).

  Definition context_match_spec : Prop :=
    forall f fs, S f fs -> exists fi, C f = Some fi /\ f_match_spec S fi fs.

  Hypothesis MATCH : context_match_spec.

  Lemma match_init_call f ret_t arg_t pre post body x m
    (FI : C f = Some (mk_f_impl arg_t ret_t body))
    (FS : S f (mk_f_spec arg_t ret_t pre post))
    (PRE : pre x m):
    wlp S (body x) (post x m) m.
  Proof.
    apply MATCH in FS as (fi' & FI' & SF).
    rewrite FI in FI'; injection FI' as ?; subst fi'.
    dependent destruction SF.
    apply MATCH0, PRE.
  Qed.

  Lemma wlp_preserved A s s' (post : A -> mem -> Prop):
    step C s s' ->
    wlp S (snd s) post (fst s) -> wlp S (snd s') post (fst s').
  Proof.
    induction 1; simpl; try solve [intuition auto].
    - (* Call *)
      intros (fpre & fpost & SF & PRE & POST).
      eapply match_init_call in PRE; try eassumption.
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
    - (* Call *)
      case WLP as (fpre & fpost & SP & _ & _).
      apply MATCH in SP as (fi & IM & MT); inversion MT; subst.
      eauto using step.
  Qed.

  Hypothesis COFREE : context_oracle_free C.

  Lemma ofree_preserved A s s'
    (OFREE : @oracle_free A (snd s)):
    step C s s' -> oracle_free (snd s').
  Proof.
    induction 1; simpl in *; intuition auto.
    - (* Call *)
      apply COFREE in GET_F.
      apply GET_F.
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

  Lemma func_okstate f arg_t ret_t pre post body x m s'
    (FI : C f = Some (mk_f_impl arg_t ret_t body))
    (FS : S f (mk_f_spec arg_t ret_t pre post))
    (PRE : pre x m)
    (STEPS : steps C (m, body x) s'):
    okstate C s'.
  Proof.
    eapply match_init_call in PRE; try eassumption.
    eapply wlp_stars_okstate, STEPS.
    - eapply COFREE in FI. apply FI.
    - exact PRE.
  Qed.
End WLP_Correct.
