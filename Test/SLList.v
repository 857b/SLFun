From SLFun Require Import Util Values SL VProg VProgGhost.
From Coq   Require Import Lists.List.

Import SLNotations SL.Tactics.
Import ListNotations.
Import VProg.Notations.


(* Singly linked lists *)

Record lcell_t := mk_lcell {
  v_data : memdata;
  v_next : ptr;
}.

Definition p_data (p : ptr) : ptr := p.
Definition p_next (p : ptr) : ptr := S p.

Definition lcell (p : ptr) (v : lcell_t) : SLprop.t :=
  vptr (p_data p) (v_data v) ** vptr (p_next p) (v_next v).


Definition lseg_t := list (ptr * memdata).

Definition lseg_entry (l : lseg_t) (sg_next : ptr) : ptr :=
  match l with
  | nil         => sg_next
  | (p, _) :: _ => p
  end.

Fixpoint lseg_sl (l : lseg_t) (sg_next : ptr) : SLprop.t :=
  match l with
  | nil          => SLprop.emp
  | (p, d) :: cs => lcell p (mk_lcell d (lseg_entry cs sg_next)) ** lseg_sl cs sg_next
  end.

Definition lseg (entry next : ptr) (v : lseg_t) : SLprop.t :=
  SLprop.pure (lseg_entry v next = entry) **
  lseg_sl v next.

Definition llist (p : ptr) : Vprop.p lseg_t :=
  lseg p NULL.
Global Arguments llist/.

(* Lemmas *)

Lemma lcell_non_null p v:
  SLprop.impp (lcell p v) (p <> NULL).
Proof.
  unfold lcell, vptr.
  eapply SLprop.impp_enough.
  SLprop.split_impp; [apply SLprop.cell_non_null | apply SLprop.impp_True].
  intro H; apply H.
Qed.

Lemma lcell_def p:
  eqv_lemma [lcell p ~>] [vptr (p_data p) ~>; vptr (p_next p) ~>]
            (fun v => (v_data v, v_next v))
            (fun dt nx => mk_lcell dt nx).
Proof.
  apply intro_eqv_lemma.
  - intros []; reflexivity.
  - intros dt nx; cbn; unfold lcell.
    SL.normalize.
    reflexivity.
Qed.

Definition intro_lseg_nil_spec : LDecl ptr unit
  FOR p FOR tt [] [] True
  RET _ FOR tt [lseg p p ~> nil] True.
Proof. Derive. Defined.
Lemma intro_lseg_nil : intro_lseg_nil_spec.
Proof.
  init_lemma p [] _; unfold lseg; SL.normalize.
  Apply; reflexivity.
Qed.

Definition elim_lseg_nil_spec : LDecl (ptr * ptr) unit
  FOR (p0, p1) FOR l [] [lseg p0 p1 ~> l] (l = nil)
  RET _ FOR tt [] (p0 = p1).
Proof. Derive. Defined.
Lemma elim_lseg_nil : elim_lseg_nil_spec.
Proof.
  init_lemma (p0, p1) l ->; unfold lseg; SL.normalize.
  Intro ->; Apply; reflexivity.
Qed.

Definition intro_lseg_cons_spec : LDecl (ptr * ptr * ptr) unit
  FOR (p0, p1, pn) FOR (hd, tl) [] [lcell p0 ~> hd; lseg p1 pn ~> tl] (v_next hd = p1)
  RET _ FOR tt [lseg p0 pn ~> ((p0, v_data hd) :: tl)] True.
Proof. Derive. Defined.
Lemma intro_lseg_cons : intro_lseg_cons_spec.
Proof.
  init_lemma ((p0, p1), pn) ([], tl) <-.
  unfold lseg; SL.normalize.
  Intro ->.
  Apply; reflexivity.
Qed.

Definition elim_lseg_cons_spec : LDecl (ptr * ptr) ptr
  FOR (p0, pn) FOR l [] [lseg p0 pn ~> l] (match l with nil => False | cons _ _ => True end)
  RET p1 FOR (dt, tl) [lcell p0 ~> (mk_lcell dt p1); lseg p1 pn ~> tl]
    (match l with nil => False | (p0', dt') :: tl' => p0' = p0 /\ dt = dt' /\ tl = tl' end).
Proof. Derive. Defined.
Lemma elim_lseg_cons : elim_lseg_cons_spec.
Proof.
  init_lemma (p0, pn) [|[p0' dt] tl] [].
  unfold lseg; cbn; Intro ->.
  Apply (lseg_entry tl pn); Apply (dt, (tl, tt)); cbn.
  Apply. repeat split.
  SL.normalize.
  Apply; reflexivity.
Qed.

Definition elim_llist_nnull_spec : LDecl ptr ptr
  FOR p0 FOR l [] [llist p0 ~> l] (p0 <> NULL)
  RET p1 FOR (dt, tl) [lcell p0 ~> (mk_lcell dt p1); llist p1 ~> tl] (l = (p0, dt) :: tl).
Proof. Derive. Defined.
Lemma elim_llist_nnull : elim_llist_nnull_spec.
Proof.
  init_lemma p0 l NNULL.
  unfold lseg; Intro <-.
  destruct l as [|[p0' dt] tl]; cbn in *.
    { exfalso; apply NNULL; reflexivity. }
  Apply (lseg_entry tl NULL); Apply (dt, (tl, tt)); cbn.
  SL.normalize.
  Apply. repeat split.
  reflexivity.
Qed.

Lemma lseg_sl_null_nil l n
  (N : lseg_entry l n = NULL):
  SLprop.impp (lseg_sl l n) (l = nil).
Proof.
  destruct l as [|[]]; cbn.
  - apply SLprop.impp_drop. reflexivity.
  - cbn in N; subst.
    eapply SLprop.impp_enough.
    SLprop.split_impp; [apply lcell_non_null | apply SLprop.impp_True].
    intuition congruence.
Qed.

Definition lseg_null_nil p pn : impp_lemma (fun l => (
  [lseg p pn ~> l], (p = NULL),
  fun _ : unit => l = nil)).
Proof.
  apply intro_impp_lemma; intros l ->.
  unfold lseg; SL.normalize.
  Intro N.
  eapply SLprop.impp_enough. apply lseg_sl_null_nil, N.
  exists tt; tauto.
Qed.

Lemma lseg_entry_app l0 l1 p2:
  lseg_entry (l0 ++ l1) p2 = lseg_entry l0 (lseg_entry l1 p2).
Proof.
  case l0; reflexivity.
Qed.

Lemma lseg_sl_app l0 l1 p2:
  SLprop.eq (lseg_sl (l0 ++ l1) p2) (lseg_sl l0 (lseg_entry l1 p2) ** lseg_sl l1 p2).
Proof.
  induction l0 as [|[] l0 IH]; cbn.
  - SL.normalize; reflexivity.
  - rewrite IH, lseg_entry_app.
    SL.normalize; reflexivity.
Qed.

Definition lseg_app_spec : LDecl (ptr * ptr * ptr) unit
  FOR (p0, p1, p2) FOR (l0, l1) [] [lseg p0 p1 ~> l0; lseg p1 p2 ~> l1] True
  RET _ FOR tt [lseg p0 p2 ~> (l0 ++ l1)] True.
Proof. Derive. Defined.
Lemma lseg_app : lseg_app_spec.
Proof.
  init_lemma ((p0, p1), p2) (l0, l1) _.
  unfold lseg.
  rewrite lseg_entry_app, lseg_sl_app; SL.normalize.
  Intro [<- <-].
  Apply; reflexivity.
Qed.


(* Implementation *)

Section Program.
  Variables (SIG : sig_context) (SPEC : ConcreteProg.spec_context SIG).

Definition Length_spec : FDecl ptr _ nat _
  FOR p
  FOR l [llist p ~> l] [] True
  RET n FOR tt [] (n = length l).
Proof. Derive. Defined.
Variable Length : Length_spec _ SPEC.

Definition Length_impl : FImpl Length := fun p0 =>
  if Mem.ptr_eq p0 NULL
  then
    gLem (lseg_null_nil p0 NULL) tt;;
    Ret 0
  else
    'g_p1 <- gLem elim_llist_nnull p0;
    gUnfold (lcell_def p0);;
    'p1 <- Read (p_next p0);
    gFold (lcell_def p0);;
    gLem replace1 (llist g_p1, llist p1);;
    (* ALT: gLem (replace [llist g_p1~>] [llist p1~>]) eq_refl;; *)
    'n  <- Length p1;
    gLem intro_lseg_cons (p0, p1, NULL);;
    Ret (S n).
Lemma Length_correct : FCorrect Length_impl.
Proof. by_wlp. Qed.
Definition Length_cp : f_extract Length_impl.
Proof. Derive. Defined.

Definition Rev_spec : FDecl (ptr * ptr) _ ptr _
  FOR (p, pr)
  FOR l [] [llist p ~> l] True
  RET r FOR tt [lseg r pr ~> rev l] True.
Proof. Derive. Defined.
Variable Rev : Rev_spec _ SPEC.

Definition Rev_impl : FImpl Rev := fun '(p0, pr) =>
  gLem intro_lseg_nil pr;;
  if Mem.ptr_eq p0 NULL
  then
    gLem (lseg_null_nil p0 NULL) tt;;
    gLem elim_lseg_nil (p0, NULL);;
    Ret pr (pt := fun r => [lseg r pr ~>])
  else
    'g_p1 <- gLem elim_llist_nnull p0;
    gUnfold (lcell_def p0);;
    'p1 <- Read (p_next p0);
    Write (p_next p0) pr;;
    gFold (lcell_def p0);;
    gLem replace1 (llist g_p1, llist p1);;
    gLem intro_lseg_cons (p0, pr, pr);;
    'r <- Rev (p1, p0);
    gLem lseg_app (r, p0, pr);;
    Ret r (pt := fun r => [lseg r pr ~>]).
Lemma Rev_correct : FCorrect Rev_impl.
Proof. by_wlp. Qed.
Definition Rev_cp : f_extract Rev_impl.
Proof. Derive. Defined.
End Program.

Section Extraction.
  Definition SIG : sig_context :=
    fun f => match f with
    | 0 => Some (fd_sig Length_spec)
    | 1 => Some (fd_sig Rev_spec)
    | _ => None
    end.

  Definition SPEC : ConcreteProg.spec_context SIG :=
    fun f => match f with
    | 0 => fd_cp Length_spec
    | 1 => fd_cp Rev_spec
    | _ => tt
    end.

  Definition H_Length := fd_mk 0 Length_spec SPEC eq_refl eq_refl.
  Definition H_Rev    := fd_mk 1 Rev_spec    SPEC eq_refl eq_refl.

  Definition IMPL : ConcreteProg.impl_context SIG :=
    fun f => match f with
    | 0 => proj1_sig (Length_cp _ _ H_Length)
    | 1 => proj1_sig (Rev_cp    _ _ H_Rev)
    | _ => tt
    end.

  Lemma match_context:
    ConcreteProg.context_match_spec IMPL SPEC.
  Proof.
    Tac.case_until_True;
    cbn beta iota delta [SIG IMPL SPEC];
    apply f_extract_match_spec.
    - apply Length_correct.
    - apply Rev_correct.
  Qed.

  Lemma context_oracle_free:
    ConcreteProg.context_oracle_free IMPL.
  Proof.
    Tac.case_until_True;
    cbn beta iota delta [SIG IMPL SPEC];
    apply f_extract_oracle_free.
  Qed.
End Extraction.
