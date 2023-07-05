From SLFun     Require Import Util Values SL VProg.Main.
From SLFun.Lib Require Malloc.

Import Util.List.
Import SLNotations ListNotations VProg.Main.Notations FunProg.Notations.
Import SL.Tactics.

(* Singly linked lists *)

Section Definitions.

(* list cell *)

Record lcell_t := mk_lcell {
  v_data : memdata;
  v_next : ptr;
}.

Definition p_data (p : ptr) : ptr := p.
Definition p_next (p : ptr) : ptr := S p.

(* The vprop for list cell is defined using [VRecord], which provides
   automatic introduction and elimination rules during the generation of
   the functional specification. *)
Lemma lcell_p (p : ptr):
  VRecord.p lcell_t [vptr (p_data p) ~>; vptr (p_next p) ~>]
    (fun v => (v_data v, v_next v))
    (fun dt nx => mk_lcell dt nx).
Proof.
  constructor; cbn; reflexivity.
Qed.

Definition lcell (p : ptr) : Vprop.p lcell_t := VRecord.v (lcell_p p).
Global Arguments lcell : simpl never.

(* list segment *)

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

(* [lseg entry next] is a [Vprop.p lseg_t].
   [lseg entry next ~>] is a [Vprop.t].
   [lseg entry next ~> sel] is a [CTX.atom] whose semantics is [lseg entry next sel]. *)
Definition lseg (entry next : ptr) (v : lseg_t) : SLprop.t :=
  SLprop.pure (lseg_entry v next = entry) **
  lseg_sl v next.

(* [llist] is just an alias for a null-terminated segment. *)
Definition llist (p : ptr) : Vprop.p lseg_t :=
  lseg p NULL.
Global Arguments llist/.

End Definitions.

Section Lemmas.

(* [SLprop.impp h P] (implies pure) expresses that the pure propostion [P] is
   satisfied if the separation logic predicate [h] is satisfied on some heap. *)
Lemma lcell_non_null p v:
  SLprop.impp (lcell p v) (p <> NULL).
Proof.
  unfold lcell; SL.normalize.
  eapply SLprop.impp_enough.
  SLprop.split_impp; [apply SLprop.cell_non_null | apply SLprop.impp_True].
  intro H; apply H.
Qed.

(* The instructions [gUnfold (lcell_def p)] and [gFold (lcell_def p)]
   can be used to unfold or fold an [lcell p].
   But this is also done automatically thanks to the automatic intro/elim rules. *)
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

(* Called automatically to expose the underlying [VRecord] and the triggering of
   intro/elim rules. *)
Definition lcell_unfold p sl:
  CTX.Trf.Tac.unfold_rule (lcell p ~> sl) (VRecord.v (lcell_p p) ~> sl).
Proof.
  reflexivity.
Qed.

(* Lemma to create/destruct a list cell from/to a free range of memory,
   using [Malloc.make_struct]/[Malloc.unmake_struct]. *)
Global Instance lcell_Struct : Malloc.Struct lcell 2.
Proof.
  split; intro p.
  rewrite Malloc.split_free_range with (n := 1),
          !Malloc.free_range_1,
          PeanoNat.Nat.add_1_r
       by (cbn; auto).
  unfold Malloc.free_cell, lcell; SL.normalize.
  apply SLprop.eq_iff_imp; split.
  - Intro v0; Intro v1; Apply (mk_lcell v0 v1); SL.normalize; reflexivity.
  - Intro [v0 v1]; Apply v0; Apply v1; SL.normalize; reflexivity.
Qed.

(* A specification (for a function or a lemma) is declared using the following notation (from [VProg.Core]):
     SPEC (args : args_ty) & (gargs : garg_ty)
     'sel0 prs_ctx pre_ctx req & REQ
     '(res : res_ty) & (gres : gres_ty) sel1 post_ctx ens
   where:
   - [args] is a pattern for the arguments of the function
   - [gargs] is an optional pattern for the ghost arguments
   - [sel0] binds the input selectors. Each input selector must occur exactly once as
     the selector of a vprop of [prs_ctx] or [pre_ctx].
   - [prs_ctx] is the preserved context, that is a list of [atom] that are present in the context
     at the beginning of the function and that must be restored (with the same selector)
     at its end.
   - [pre_ctx] is the precondition context, [atom] present only at the beginning of the function.
   - [req] (requires) is a proposition that expresses a precondition on the arguments and
     on the input selectors.
     It can optionally be bound with [& REQ] to be used in [post_ctx] and [ens].
   - [res] is a name that binds the returned value.
   - [gres] is an optional name for the ghost returned value.
   - [sel1] binds the output selectors.
   - [post_ctx] is the postcondition context.
   - [ens] (ensures) is a proposition expressing a postcondition.
     It can depend on all the previously bound variables.
   There are the following restrictions, that can trigger an error either at the declaration or at the use:
   - Each input selectors mist occur exactly once as the selector of a vprop of [prs_ctx] or [pre_ctx].
   - All selectors of [prs_ctx] and [pre_ctx] must be variables from [sel0].
   - One cannot pattern match on the returned value (or on the ghost one), if it is a record, one must use
     projections in [post_ctx].
   - The vprops of [post_ctx] must be independents of [sel1], but their selectors can and can also
     be arbitrary expressions not necessarily variables of [sel1].
 *)
Derive intro_lseg_nil_spec SuchThat (
  VLem SPEC (p : ptr)
  'tt [] [] True
  '(_ : unit) tt [lseg p p ~> nil] True
  intro_lseg_nil_spec) As intro_lseg_nil.
Proof.
  init_lemma p [] ?; unfold lseg; SL.normalize.
  (* A lemma is just an heap entailment in the underlying separation logic.
     It can be called from a program with the [gLem] instruction. *)
  Apply; reflexivity.
Qed.

(* The [intro_lseg_nil] lemma can be called to explicitly introduce a [lseg p p]
   in the context.
   But the following rule can do it automatically. *)
Lemma lseg_nil_intro_rule p sl :
  CTX.Trf.Tac.intro_rule true
    (lseg p p ~> sl) []
    (sl = []) True.
Proof.
  constructor; intros ->; cbn.
  unfold lseg; SL.normalize.
  erewrite SLprop.impp_eq. { SL.normalize; reflexivity. }
  apply SLprop.impp_drop; reflexivity.
Qed.


Derive elim_lseg_nil_spec SuchThat (
  VLem SPEC ((p0, p1) : ptr * ptr)
  'l [] [lseg p0 p1 ~> l] (l = nil)
  '(_ : unit) tt [] (p0 = p1)
  elim_lseg_nil_spec) As elim_lseg_nil.
Proof.
  init_lemma (p0, p1) l ->; unfold lseg; SL.normalize.
  Intro ->; Apply; reflexivity.
Qed.

Derive intro_lseg_cons_spec SuchThat (
  VLem SPEC ((p0, p1, pn) : ptr * ptr * ptr)
  '(hd, tl) [] [lcell p0 ~> hd; lseg p1 pn ~> tl] (v_next hd = p1)
  '(_ : unit) tt [lseg p0 pn ~> ((p0, v_data hd) :: tl)] True
  intro_lseg_cons_spec) As intro_lseg_cons.
Proof.
  init_lemma ((p0, p1), pn) ([], tl) <-.
  unfold lseg; SL.normalize.
  Intro ->.
  Apply; reflexivity.
Qed.

(* We cannot use the following specification:
     SPEC ((p0, pn) : ptr * ptr)
     '(hd, tl) [] [lseg p0 pn ~> hd :: tl] True
     '(p1 : ptr) tt [lcell p0 ~> (mk_lcell (snd hd) p1); lseg p1 pn ~> tl] (p0 = fst hd).
   Because [lseg p0 pn] would have a selector which is not a variable.
   Instead, we assert that its selector is a [cons] in the requires clause
   and use this fact in the postcondition and in the ensures clause.
   Another option would have been to return fresh variables [hd] and [tl] and
   assert that [l = hd :: tl] in the ensures clause.
 *)
Derive elim_lseg_cons_spec SuchThat (
  VLem SPEC ((p0, pn) : ptr * ptr)
  'l [] [lseg p0 pn ~> l] (is_cons l)&REQ
  '(p1 : ptr) tt [lcell p0 ~> (mk_lcell (snd (hd_tot l REQ)) p1); lseg p1 pn ~> tl_tot l REQ]
    (p0 = fst (hd_tot l REQ))
  elim_lseg_cons_spec) As elim_lseg_cons.
Proof.
  init_lemma (p0, pn) [|[p0' dt] tl] [].
  unfold lseg; cbn; Intro ->.
  Apply (lseg_entry tl pn); cbn.
  Apply. reflexivity.
  SL.normalize.
  Apply; reflexivity.
Qed.

Derive elim_llist_nnull_spec SuchThat (
  VLem SPEC (p0 : ptr)
  'l [] [llist p0 ~> l] (p0 <> NULL)
  '(p1 : ptr) (dt, tl) [lcell p0 ~> (mk_lcell dt p1); llist p1 ~> tl] (l = (p0, dt) :: tl)
  elim_llist_nnull_spec) As elim_llist_nnull.
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

(* An [impp_lemma] is a lemma that derives a pure proposition from the program context. *)
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

Derive lseg_app_spec SuchThat (
  VLem SPEC ((p0, p1, p2) : ptr * ptr * ptr)
  '(l0, l1) [] [lseg p0 p1 ~> l0; lseg p1 p2 ~> l1] True
  '(_ : unit) tt [lseg p0 p2 ~> (l0 ++ l1)] True
  lseg_app_spec) As lseg_app.
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

Variables
  (Init   : Malloc.Init_spec   CT)
  (Malloc : Malloc.Malloc_spec CT).

(* Set up automatic intro/elim of vprops *)
Local Hint Resolve lcell_unfold | 1 : CtxTrfDB.
Hint Extern 1 (CTX.Trf.Tac.intro_rule _ (lseg ?p ?p ~> ?sl) _ _ _) =>
  exact (lseg_nil_intro_rule p sl) : CtxTrfDB.
Import VRecord.Tactics VGroup.Tactics.


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
    gRewrite g_p1 p1;;
      (* Replaces [g_p1] with [p1] everywhere in the context.
         Explicit alternatives here would be:
           [gLem replace1 (llist g_p1, llist p1)]
           [gLem (replace [llist g_p1~>] [llist p1~>]) eq_refl]
       *)
    'n  <- Length p1;
    gLem intro_lseg_cons (p0, p1, NULL);;
    Ret (S n).
Lemma Length_correct : FCorrect Length_impl.
Proof.
  (* Build a functional specification for the function. *)
  build_fun_spec.
  (* Build a WLP from the functional specification. *)
  FunProg.by_wlp.
  (* Tactic to solve a WLP, mostly do the same thing as [intuition] but also destructs values
     that appear in a [match]. *)
  FunProg.solve_wlp; auto.
Qed.


(* A program fragment to do a case analysis on a linked list *)
Definition llist_case_res (p : ptr) (r : option ptr) : Vprop.p _ :=
  vgroup match r with
  | None    => []
  | Some p1 => [lcell p~>; llist p1~>]
  end.
Global Arguments llist_case_res/.
Definition llist_case_spec : FDecl SPEC
  (p : ptr) 'l [] [llist p ~> l] True
  '(r : option ptr) v [llist_case_res p r ~> v]
    (match r as r return VpropList.sel_t (if r then _ else _) -> Prop with
     | None    => fun _ => p = NULL /\ l = nil
     | Some p1 => Tuple.to_fun (TS := VpropList.sel [lcell p~>; llist p1~>]) (fun x l' =>
                  p <> NULL /\ l = (p, v_data x) :: l' /\ v_next x = p1)
     end v).
Proof. Derived. Defined.

Definition llist_case_impl : FragImpl llist_case_spec CT := fun p =>
  if Mem.ptr_eq p NULL
  then
    gLem (lseg_null_nil p NULL) tt;;
    gLem elim_lseg_nil (p, NULL);;
    Ret None
  else
    'g_p1 <- gLem elim_llist_nnull p;
    'p1 <- Read (p_next p);
    gRewrite g_p1 p1;;
    Ret (Some p1).
Lemma llist_case : FragCorrect llist_case_impl.
Proof. solve_by_wlp. Qed.


(* Alternative implementation using the [llist_case] fragment *)
Definition Length_impl_frag : FImpl Length := fun p0 =>
  'r <- llist_case p0;
  match r with
  | None =>
      (* gLem elim_empty_group tt;; *)
      gLem replace1 (llist NULL, llist p0);;
      Ret 0
  | Some p1 =>
      'n <- Length p1;
      gLem intro_lseg_cons (p0, p1, NULL);;
      Ret (S n)
  end.
Lemma Length_frag_correct : FCorrect Length_impl_frag.
Proof. solve_by_wlp. Qed.


(* Alternative implementation using a loop. *)
Definition loop_ptr (x : ptr * nat + nat) : ptr :=
  match x with
  | inl (p, _) => p
  | inr _      => NULL
  end.
Definition Length_impl_loop : FImpl Length := fun p0 =>
  gLem intro_lseg_nil p0;;
  let inv (x : ptr * nat + nat) :=
    let p1 := loop_ptr x in
    [lseg p0 p1~>; llist p1~>]
  in
  'n <- Loop (inv := inv) (inl (p0, 0)) (fun '(p1, n) =>
    if Mem.ptr_eq p1 NULL
    then
      gRewrite p1 NULL;;
      Ret (inr n)
    else
      'g_p2 <- gLem elim_llist_nnull p1;
      'p2 <- Read (p_next p1);
      gRewrite g_p2 p2;;
      (* gLem intro_lseg_nil p2;; implicit using lseg_nil_intro_rule *)
      gLem intro_lseg_cons (p1, p2, p2);;
      gLem lseg_app (p0, p1, p2);;
      Ret (inl (p2, (S n)))
  );
  gLem (lseg_null_nil NULL NULL) tt;;
  gLem elim_lseg_nil (NULL, NULL);;
  Ret n.
Lemma Length_loop_correct : FCorrect Length_impl_loop.
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
  (* instantiate the loop invariant *)
  exists (fun x l0 l1 =>
    let n := match x with inl (_, n) | inr n => n end in
    sel0 = l0 ++ l1 /\ n = length l0
  ).
  FunProg.solve_wlp; autorewrite with list; auto.
  - rewrite <- List.app_assoc; reflexivity.
  - rewrite PeanoNat.Nat.add_comm; reflexivity.
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
    Ret pr
  else
    'g_p1 <- gLem elim_llist_nnull p0;
    'p1 <- Read (p_next p0);
    Write (p_next p0) pr;;
    gRewrite g_p1 p1;;
    gLem intro_lseg_cons (p0, pr, pr);;
    'r <- Rev (p1, p0);
    gLem lseg_app (r, p0, pr);;
    Ret r.
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
      gRewrite g_p1 p1;;
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
Qed.


Definition Main_spec : FDecl SPEC
  (_ : unit)
  'u [] [Malloc.full_mem ~> u] True
  '(r : nat) tt [vtrue ~> tt] (r = 1).
Proof. Derived. Defined.
Variable Main : Main_spec CT.

Definition Main_impl : FImpl Main := fun _ =>
  Init tt;;
  'p <- Malloc 2;
  gLem (Malloc.make_struct lcell) p;;
  Write (p_next p) NULL;;
  gLem intro_lseg_cons (p, NULL, NULL);;
  'r <- Length p;
  gLem intro_true (vgroup [Malloc.malloc_env ~>; Malloc.allocated p ~>; llist p ~>]);;
  Ret r.
Lemma Main_correct : FCorrect Main_impl.
Proof.
  build_fun_spec.
  FunProg.solve_by_wlp.
Qed.

End Program.

(* We combine the different functions into a concrete program.
   This also removes the ghost code (erasure) and resolves the dependencies between the functions,
   which can fail. *)
Derive prog SuchThat (ConcreteProg.of_entries [
  f_entry Main_spec          Main_correct;
  f_entry Malloc.Init_spec   Malloc.Init_correct;
  f_entry Malloc.Malloc_spec Malloc.Malloc_correct;
  f_entry Length_spec        Length_loop_correct;
  f_entry Rev_spec           Rev_correct;
  f_entry Seg_Next_spec      Seg_Next_correct
] prog) As prog_correct.
Proof. Derived. Qed.

(* [prog] is a tuple of function implementation: *)
(* Print prog. *)
(* [prog_correct] is a proof that they are correct with respect to their specifications. *)

(* Representation of the program as a function. *)
Definition IMPL : ConcreteProg.impl_context _ := ConcreteProg.impl_of_list prog.

(* Starting from the main function (identifier 0) and any memory, the program cannot get stuck. *)
Lemma main_okstate m s'
  (STEPS  : ConcreteProg.steps IMPL (m, ConcreteProg.get_fun_body IMPL 0 eq_refl tt) s'):
  ConcreteProg.okstate IMPL s'.
Proof.
  eapply ConcreteProg.func_okstate in STEPS; eauto.
  1,2:apply prog_correct.
  { cbn.
    eexists _, SLprop.True.
    split. 2:reflexivity.
    unfold tr_f_spec, Spec.tr, Spec.Expanded.tr; cbn.
    exists tt, tt, Logic.I; cbn; reflexivity. }
  cbn.
  eapply SLprop.mem_match_sl_morph; try SL.normalize.
  apply Malloc.match_full_mem.
Qed.
