From SLFun Require Import Util Values SL VProg.Main.

Import Util.List.
Import SLNotations ListNotations VProg.Main.Notations FunProg.Notations.
Import SL.Tactics.

(* Singly linked lists *)

Section Definitions.

Record lcell_t := mk_lcell {
  v_data : memdata;
  v_next : ptr;
}.

Definition p_data (p : ptr) : ptr := p.
Definition p_next (p : ptr) : ptr := S p.

Lemma lcell_p (p : ptr):
  VRecord.p lcell_t [vptr (p_data p) ~>; vptr (p_next p) ~>]
    (fun v => (v_data v, v_next v))
    (fun dt nx => mk_lcell dt nx).
Proof.
  constructor; cbn; reflexivity.
Qed.

Definition lcell (p : ptr) := VRecord.v (lcell_p p).
Global Arguments lcell : simpl never.

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

End Definitions.

Section Lemmas.

Lemma lcell_non_null p v:
  SLprop.impp (lcell p v) (p <> NULL).
Proof.
  unfold lcell; SL.normalize.
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

Definition lcell_unfold p sl:
  CTX.Trf.Tac.unfold_rule (lcell p ~> sl) (VRecord.v (lcell_p p) ~> sl).
Proof.
  reflexivity.
Qed.

Definition intro_lseg_nil_spec : LDecl SPEC
  (p : ptr) 'tt [] [] True
  '(_ : unit) tt [lseg p p ~> nil] True.
Proof. Derived. Defined.
Lemma intro_lseg_nil : intro_lseg_nil_spec.
Proof.
  init_lemma p [] ?; unfold lseg; SL.normalize.
  Apply; reflexivity.
Qed.

Definition elim_lseg_nil_spec : LDecl SPEC
  ((p0, p1) : ptr * ptr) 'l [] [lseg p0 p1 ~> l] (l = nil)
  '(_ : unit) tt [] (p0 = p1).
Proof. Derived. Defined.
Lemma elim_lseg_nil : elim_lseg_nil_spec.
Proof.
  init_lemma (p0, p1) l ->; unfold lseg; SL.normalize.
  Intro ->; Apply; reflexivity.
Qed.

Definition intro_lseg_cons_spec : LDecl SPEC
  ((p0, p1, pn) : ptr * ptr * ptr) '(hd, tl) [] [lcell p0 ~> hd; lseg p1 pn ~> tl] (v_next hd = p1)
  '(_ : unit) tt [lseg p0 pn ~> ((p0, v_data hd) :: tl)] True.
Proof. Derived. Defined.
Lemma intro_lseg_cons : intro_lseg_cons_spec.
Proof.
  init_lemma ((p0, p1), pn) ([], tl) <-.
  unfold lseg; SL.normalize.
  Intro ->.
  Apply; reflexivity.
Qed.

Definition elim_lseg_cons_spec : LDecl SPEC
  ((p0, pn) : ptr * ptr) 'l [] [lseg p0 pn ~> l] (is_cons l)&REQ
  '(p1 : ptr) tt [lcell p0 ~> (mk_lcell (snd (hd_tot l REQ)) p1); lseg p1 pn ~> tl_tot l REQ]
    (p0 = fst (hd_tot l REQ)).
Proof. Derived. Defined.
Lemma elim_lseg_cons : elim_lseg_cons_spec.
Proof.
  init_lemma (p0, pn) [|[p0' dt] tl] [].
  unfold lseg; cbn; Intro ->.
  Apply (lseg_entry tl pn); cbn.
  Apply. reflexivity.
  SL.normalize.
  Apply; reflexivity.
Qed.

Definition elim_llist_nnull_spec : LDecl SPEC
  (p0 : ptr) 'l [] [llist p0 ~> l] (p0 <> NULL)
  '(p1 : ptr) (dt, tl) [lcell p0 ~> (mk_lcell dt p1); llist p1 ~> tl] (l = (p0, dt) :: tl).
Proof. Derived. Defined.
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

Definition lseg_app_spec : LDecl SPEC
  ((p0, p1, p2) : ptr * ptr * ptr) '(l0, l1) [] [lseg p0 p1 ~> l0; lseg p1 p2 ~> l1] True
  '(_ : unit) tt [lseg p0 p2 ~> (l0 ++ l1)] True.
Proof. Derived. Defined.
Lemma lseg_app : lseg_app_spec.
Proof.
  init_lemma ((p0, p1), p2) (l0, l1) ?.
  unfold lseg.
  rewrite lseg_entry_app, lseg_sl_app; SL.normalize.
  Intro [<- <-].
  Apply; reflexivity.
Qed.

End Lemmas.

Section Program.
  Variable CT : ConcreteProg.context.

Local Hint Resolve lcell_unfold | 1 : CtxTrfDB.
Import VRecord.Tactics.

Definition Length_spec : FDecl SPEC
  (p : ptr)
  'l [llist p ~> l] [] True
  '(n : nat) tt [] (n = length l).
Proof. Derived. Defined.
Variable Length : Length_spec CT.

Definition Length_impl : FImpl Length := fun p0 =>
  if Mem.ptr_eq p0 NULL
  then
    gLem (lseg_null_nil p0 NULL) tt;;
    Ret 0
  else
    'g_p1 <- gLem elim_llist_nnull p0;
    'p1 <- Read (p_next p0);
    gLem replace1 (llist g_p1, llist p1);;
    (* ALT: gLem (replace [llist g_p1~>] [llist p1~>]) eq_refl;; *)
    'n  <- Length p1;
    gLem intro_lseg_cons (p0, p1, NULL);;
    Ret (S n).
Lemma Length_correct : FCorrect Length_impl.
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.


Definition Rev_spec : FDecl SPEC
  ((p, pr) : ptr * ptr)
  'l [] [llist p ~> l] True
  '(r : ptr) tt [lseg r pr ~> rev l] True.
Proof. Derived. Defined.
Variable Rev : Rev_spec CT.

Definition Rev_impl : FImpl Rev := fun '(p0, pr) =>
  gLem intro_lseg_nil pr;;
  if Mem.ptr_eq p0 NULL
  then
    gLem (lseg_null_nil p0 NULL) tt;;
    gLem elim_lseg_nil (p0, NULL);;
    Ret pr (pt := fun r => [lseg r pr ~>])
  else
    'g_p1 <- gLem elim_llist_nnull p0;
    'p1 <- Read (p_next p0);
    Write (p_next p0) pr;;
    gLem replace1 (llist g_p1, llist p1);;
    gLem intro_lseg_cons (p0, pr, pr);;
    'r <- Rev (p1, p0);
    gLem lseg_app (r, p0, pr);;
    Ret r (pt := fun r => [lseg r pr ~>]).
Lemma Rev_correct : FCorrect Rev_impl.
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

Definition Seg_Next_spec : FDecl SPEC
  ((p, n) : ptr * nat) & (pn : ptr)
  'l [lseg p pn ~> l] [] (n = length l)
  '(r : ptr) tt [] (r = pn).
Proof. Derived. Defined.
Variable Seg_Next : Seg_Next_spec CT.

Definition Seg_Next_impl : FImpl Seg_Next := fun '(p, n) pn =>
  match n with
  | O   =>
      gExploit [lseg p pn~>];;
      Ret p
  | S n =>
      'g_p1 <- gLem elim_lseg_cons (p, pn);
      'p1 <- Read (p_next p);
      gLem replace1 (lseg g_p1 pn, lseg p1 pn);;
      'r <- Seg_Next (p1, n) pn;
      gLem intro_lseg_cons (p, p1, pn);;
      Ret r
  end.
Lemma Seg_Next_correct : FCorrect Seg_Next_impl.
Proof.
  build_fun_spec.
  FunProg.by_wlp.
  case n as [|n]; destruct sel0; simplify_eq 1; FunProg.solve_wlp.
  - apply H; unfold lseg; SL.normalize.
    Intro E; auto.
  - destruct p0; reflexivity.
Qed.

End Program.

Derive prog SuchThat (ConcreteProg.of_entries [
  f_entry Length_spec    Length_correct;
  f_entry Rev_spec       Rev_correct;
  f_entry Seg_Next_spec  Seg_Next_correct
] prog) As prog_correct.
Proof. Derived. Qed.
