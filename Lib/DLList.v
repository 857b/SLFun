From SLFun Require Import Util Values SL VProg.Main.

Import Util.List.
Import ListNotations SLNotations VProg.Main.Notations FunProg.Notations.
Import SL.Tactics.

(* Doubly linked lists *)

Module Param.
  Local Set Implicit Arguments.

  Record lcell_t (D : Type) : Type := mk_lcell {
    data : D;
    prev : ptr;
    next : ptr;
  }.

  Definition set_prev [D] (prev : ptr) (c : lcell_t D) : lcell_t D :=
    {| data := data c; prev := prev; next := next c |}.

  Definition set_next [D] (next : ptr) (c : lcell_t D) : lcell_t D :=
    {| data := data c; prev := prev c; next := next |}.

  Record vp : Type := {
    data_t : ptr -> Type;
    vcell  : forall p : ptr, Vprop.p (lcell_t (data_t p));
    vcell_non_null : forall p v,
      SLprop.impp (@vcell p v) (p <> NULL)
  }.

  Definition sel_t (vP : vp) (p : ptr) : Type := lcell_t (data_t vP p).

  Section Fragments.
    Variable vP : vp.

    Definition read_ref_spec (get : forall p : ptr, sel_t vP p -> ptr) : FDecl SPEC
      (p : ptr) 'c [vcell vP p ~> c] [] True
      '(r : ptr) tt [] (r = get p c).
    Proof. Derived. Defined.

    Definition write_ref_spec (set : forall p : ptr, ptr -> sel_t vP p -> sel_t vP p) : FDecl SPEC
      ((p, r) : ptr * ptr) 'c [] [vcell vP p ~> c] True
      '(_ : unit) tt [vcell vP p ~> set p r c] True.
    Proof. Derived. Defined.

    Record impl (CT : ConcreteProg.context) : Type := {
      read_prev  : Frag (read_ref_spec  (fun p => @prev _)) CT;
      write_prev : Frag (write_ref_spec (fun p => @set_prev _)) CT;
      read_next  : Frag (read_ref_spec  (fun p => @next _)) CT;
      write_next : Frag (write_ref_spec (fun p => @set_next _)) CT;
    }.
  End Fragments.
End Param.

Section DLList.
  Import Param.
  Variable vP : Param.vp.

Section Definitions.
  (* Doubly linked list segment:

                 first                    last
           ----> ,---, ----> ,---, ----> ,---, ---->
      prev       |   |       |   |       |   |       next
           <---- '---' <---- '---' <---- '---' <----

     NOTE: for an empty segment, [last = prev] and [first = next]
   *)

  Definition lseg_t := list {p : ptr & data_t vP p}.


  Definition lseg_first (l : lseg_t) (sg_next : ptr) : ptr :=
    match l with
    | nil               => sg_next
    | existT _ p _ :: _ => p
    end.

  Fixpoint lseg_last (sg_prev : ptr) (l : lseg_t) {struct l} : ptr :=
    match l with
    | nil               => sg_prev
    | existT _ p _ :: l => lseg_last p l
    end.

  Fixpoint lseg_sl (sg_prev : ptr) (l : lseg_t) (sg_next : ptr) {struct l} : SLprop.t :=
    match l with
    | nil =>
        SLprop.emp
    | (existT _ p d) :: l =>
        vcell vP p {| data := d; prev := sg_prev; next := lseg_first l sg_next |} **
        lseg_sl p l sg_next
    end.

  Definition lseg (prev first next : ptr) (l : lseg_t) : SLprop.t :=
    SLprop.pure (lseg_first l next = first) **
    lseg_sl prev l next.

  Definition llist (p : ptr) : Vprop.p lseg_t :=
    lseg NULL p NULL.
  Global Arguments llist/.
End Definitions.

Section Lemmas.

  Derive intro_lseg_nil_spec SuchThat (
    VLem SPEC ((prev, next) : ptr * ptr)
    'tt [] [] True
    '(_ : unit) tt [lseg prev next next ~> nil] True
    intro_lseg_nil_spec) As intro_lseg_nil.
  Proof.
    init_lemma (prev, next) [] ?; unfold lseg; SL.normalize.
    Apply. auto.
    reflexivity.
  Qed.

  Lemma lseg_nil_intro_rule prev next sl :
    CTX.Trf.Tac.intro_rule true
      (lseg prev next next ~> sl) []
      (sl = []) True.
  Proof.
    constructor; intros ->; cbn.
    unfold lseg; SL.normalize.
    erewrite SLprop.impp_eq. { SL.normalize; reflexivity. }
    apply SLprop.impp_drop; auto.
  Qed.

  Derive elim_lseg_nil_spec SuchThat (
    VLem SPEC ((prev, first, next) : ptr * ptr * ptr)
    'l [] [lseg prev first next ~> l] (l = nil)
    '(_ : unit) tt [] (first = next)
    elim_lseg_nil_spec) As elim_lseg_nil.
  Proof.
    init_lemma ((prev, first), next) l ->; unfold lseg; SL.normalize.
    Intro ->; Apply; reflexivity.
  Qed.

  Derive intro_lseg_cons_spec SuchThat (
    VLem SPEC ((pr, p0, p1, pn) : ptr * ptr * ptr * ptr)
    '(hd, tl) [] [vcell vP p0 ~> hd; lseg p0 p1 pn ~> tl] (prev hd = pr /\ next hd = p1)
    '(_ : unit) tt [lseg pr p0 pn ~> (existT _ p0 (data hd)) :: tl] True
    intro_lseg_cons_spec) As intro_lseg_cons.
  Proof.
    init_lemma (((pr, p0), p1), pn) ([], tl) [<- <-].
    unfold lseg; SL.normalize.
    Intro <-.
    Apply. auto.
    reflexivity.
  Qed.

  Derive elim_lseg_cons_spec SuchThat (
    VLem SPEC ((pr, p0, pn) : ptr * ptr * ptr)
    'l [] [lseg pr p0 pn ~> l] (is_cons l)&REQ
    '(p1 : ptr) hd [vcell vP p0 ~> {| data := hd; prev := pr; next := p1 |}; lseg p0 p1 pn ~> tl_tot l REQ]
      (hd_tot l REQ = existT _ p0 hd)
    elim_lseg_cons_spec) As elim_lseg_cons.
  Proof.
    init_lemma ((pr, p0), pn) [|[p0' hd] tl] [].
    unfold lseg; cbn.
    Intro ->.
    Apply (lseg_first tl pn); Apply (hd, tt); SL.normalize.
    Apply. auto.
    reflexivity.
  Qed.

  Derive elim_lseg_nnull_spec SuchThat (
    VLem SPEC ((pr, p0) : ptr * ptr)
    'l [] [lseg pr p0 NULL ~> l] (p0 <> NULL)
    '(p1 : ptr) (hd, tl) [vcell vP p0 ~> {| data := hd; prev := pr; next := p1 |}; lseg p0 p1 NULL ~> tl]
       (l = existT _ p0 hd :: tl)
    elim_lseg_nnull_spec) As elim_lseg_nnull.
  Proof.
    init_lemma (pr, p0) l NNULL.
    unfold lseg; Intro <-.
    destruct l as [|[p0' hd] tl]; cbn in *.
      { exfalso; apply NNULL; reflexivity. }
    Apply (lseg_first tl NULL); Apply (hd, (tl, tt)); SL.normalize.
    Apply. auto.
    reflexivity.
  Qed.


  Lemma lseg_sl_null_nil l pr pn
    (N : lseg_first l pn = NULL):
    SLprop.impp (lseg_sl pr l pn) (l = nil).
  Proof.
    destruct l as [|[]]; cbn.
    - apply SLprop.impp_drop. reflexivity.
    - cbn in N; subst.
      eapply SLprop.impp_enough.
      SLprop.split_impp; [apply vcell_non_null | apply SLprop.impp_True].
      intuition congruence.
  Qed.

  Lemma lseg_null_nil pr p pn : impp_lemma (fun l => (
    [lseg pr p pn ~> l], (p = NULL),
    fun _ : unit => l = nil)).
  Proof.
    apply intro_impp_lemma; intros l ->.
    unfold lseg; SL.normalize.
    Intro N.
    eapply SLprop.impp_enough. eapply lseg_sl_null_nil, N.
    exists tt; tauto.
  Qed.


  Lemma lseg_first_app l0 l1 p2:
    lseg_first (l0 ++ l1) p2 = lseg_first l0 (lseg_first l1 p2).
  Proof.
    case l0; reflexivity.
  Qed.

  Lemma lseg_sl_app l0 l1 pr pn:
    SLprop.eq (lseg_sl pr (l0 ++ l1) pn) (lseg_sl pr l0 (lseg_first l1 pn)** lseg_sl (lseg_last pr l0) l1 pn).
  Proof.
    revert pr; induction l0 as [|[] l0 IH]; intro; cbn;
      [|rewrite IH, lseg_first_app];
      SL.normalize; reflexivity.
  Qed.

  Derive lseg_app_spec SuchThat (
    VLem SPEC ((pr, pf0, pl0, pf1, pn) : ptr * ptr * ptr * ptr * ptr)
    '(l0, l1) [] [lseg pr pf0 pf1 ~> l0; lseg pl0 pf1 pn ~> l1] (lseg_last pr l0 = pl0)
    '(_ : unit) tt [lseg pr pf0 pn ~> (l0 ++ l1)] True
    lseg_app_spec) As lseg_app.
  Proof.
    init_lemma ((((pr, pf0), pl0), pf1), pn) (l0, l1) <-.
    unfold lseg; SL.normalize.
    Intro [<- <-].
    rewrite lseg_sl_app, lseg_first_app.
    Apply; reflexivity.
  Qed.
End Lemmas.

Section Impl.
  Variables (CT : ConcreteProg.context) (iP : Param.impl vP CT).

  Import VGroup.Tactics.
  Hint Extern 1 (CTX.Trf.Tac.intro_rule _ (lseg ?prev ?p ?p ~> ?sl) _ _ _) =>
    exact (lseg_nil_intro_rule prev p sl) : CtxTrfDB.


  Definition lseg_case_res (p : ptr) (r : option ptr) : Vprop.p _ :=
    vgroup match r with
    | None    => []
    | Some p1 => [vcell vP p~>; lseg p p1 NULL~>]
    end.
  Global Arguments lseg_case_res/.

  Definition lseg_case_res_sel (pr : ptr) (p : ptr) (r : option ptr):
      forall v : match r with None => unit | Some p1 => data_t vP p * lseg_t end,
      Vprop.ty (lseg_case_res p r ~>) :=
    match r with
    | None    => fun     _    => tt
    | Some p1 => fun '(x, tl) => ({| data := x; prev := pr; next := p1 |}, (tl, tt))
    end.

  Definition lseg_case_spec : FDecl SPEC
    (p : ptr) & (pr : ptr) 'l [] [lseg pr p NULL ~> l] True
    '(r : option ptr) v [lseg_case_res p r ~> lseg_case_res_sel pr p r v]
      (match r as r return (if r then _ else _) -> Prop with
       | None    => fun     _    => p =  NULL /\ l = nil
       | Some p1 => fun '(x, tl) => p <> NULL /\ l = existT _ p x :: tl
       end v).
  Proof. Derived. Defined.

  Definition lseg_case_impl : FragImpl lseg_case_spec CT := fun p pr =>
    if Mem.ptr_eq p NULL
    then
      gLem (lseg_null_nil pr p NULL) tt;;
      gLem elim_lseg_nil (pr, p, NULL);;
      Ret None
    else
      'g_p1 <- gLem elim_lseg_nnull (pr, p);
      'p1   <- read_next iP p;
      gRewrite g_p1 p1;;
      Ret (Some p1).
  Lemma lseg_case : FragCorrect lseg_case_impl.
  Proof.
    solve_by_wlp.
    - exists tt; auto.
    - eexists (_, _); eauto.
  Qed.


  Definition Length_spec : FDecl SPEC
    (p : ptr) & (pr : ptr)
    'l [lseg pr p NULL ~> l] [] True
    '(n : nat) tt [] (n = length l).
  Proof. Derived. Defined.
  Variable Length : Length_spec CT.

  Definition Length_impl : FImpl Length := fun p0 pr =>
    'r <- lseg_case p0 pr;
    match r with
    | None =>
        gLem replace1 (lseg pr NULL NULL, lseg pr p0 NULL);;
        Ret 0
    | Some p1 =>
        'n <- Length p1 p0;
        gLem intro_lseg_cons (pr, p0, p1, NULL);;
        Ret (S n)
    end.
  Lemma Length_correct : FCorrect Length_impl.
  Proof. solve_by_wlp. Qed.

End Impl.

  Definition entries := [
    f_entry Length_spec   Length_correct
  ].
End DLList.
