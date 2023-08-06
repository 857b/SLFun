From SLFun Require Import Util Values SL VProg.Main.
From Coq   Require Import Lia.

Import Util.List.
Import ListNotations SLNotations VProg.Main.Notations FunProg.Notations.
Import SL.Tactics.

(* Toy memory allocator *)

Definition free_cell (p : ptr) : SLprop.t :=
  SLprop.ex memdata (SLprop.cell p).

Definition le_opt (n : nat) (m : option nat) : Prop :=
  match m with
  | Some m => n <= m
  | None   => True
  end.

Definition in_range (p0 : ptr) (len : option nat) (p : ptr) : Prop :=
  p0 <= p /\ le_opt (S (p - p0)) len.

Definition free_range (p0 : ptr) (len : option nat) : SLprop.t :=
  SLprop.all_sub eq (in_range p0 len) free_cell.

Definition full_mem : Vprop.p unit :=
  fun _ => free_range 1 None.

Definition p_next_free : ptr := 1.

Definition malloc_env : Vprop.p unit :=
  fun _ => SLprop.ex nat (fun next_free =>
  vptr p_next_free next_free ** free_range next_free None ** SLprop.True)%slprop.

(* A vprop that can be used by the allocator to represent the fact that a range was allocated
   an can be freed. Unused by our toy allocator. *)
Definition allocated (p : ptr) : Vprop.p nat :=
  fun n => SLprop.emp.

(* C-like structures that can be created/destructed from/to a [free_range]. *)
Class Struct [A : ptr -> Type] (v : forall p : ptr, Vprop.p (A p)) (len : nat) : Prop := mk_Struct {
  struct_E : forall p : ptr, SLprop.eq (free_range p (Some len)) (SLprop.ex (A p) (v p))
}.

Section Lemmas.

Lemma free_range_0 p0:
  SLprop.eq (free_range p0 (Some O)) SLprop.emp.
Proof.
  apply SLprop.all_0; auto.
  intros [p [H0 H1]]; exfalso.
  cbn in H1; lia.
Qed.

Lemma free_range_1 p0:
  SLprop.eq (free_range p0 (Some 1)) (free_cell p0).
Proof.
  assert (R0 : forall p, in_range p0 (Some 1) p <-> p = p0)
    by (unfold in_range; cbn; intuition lia).
  apply SLprop.all_1.
  - intros [? H0] [? H1]; cbn; apply R0 in H0 as ->, H1 as ->; reflexivity.
  - intros [? H]; cbn; apply R0 in H as ->; reflexivity.
  - constructor; exists p0; apply R0; reflexivity.
Qed.

Lemma split_free_range p0 len n
  (LE : le_opt n len):
  SLprop.eq
    (free_range p0 len)
    (free_range p0 (Some n) ** free_range (p0 + n) (option_map (fun m => m - n) len)).
Proof.
  unfold free_range, SLprop.all_sub.
  etransitivity. {
    apply SLprop.all_split with (f := fun p => Nat.leb (S (proj1_sig p - p0)) n); auto.
    Rel.by_expr (Rel.pull (@proj1_sig ptr (in_range p0 len)) eq).
  }
  unfold SLprop.all_sub at 1 2.
  rewrite (SLprop.all_sub_conj _ (in_range p0 len) (fun p => Nat.leb (S (p - p0)) n = true )),
          (SLprop.all_sub_conj _ (in_range p0 len) (fun p => Nat.leb (S (p - p0)) n = false))
       by (auto; intros; subst; reflexivity).
  apply SLprop.star_morph_eq;
  apply SLprop.all_sub_iff;
    try solve [auto; intros; subst; reflexivity];
  intro p.
  - rewrite PeanoNat.Nat.leb_le.
    unfold in_range; intuition.
    destruct len; cbn in LE, H1 |- *; lia.
  - rewrite Compare_dec.leb_iff_conv.
    unfold in_range; intuition; try lia;
    destruct len; cbn in *; lia.
Qed.

Lemma match_full_mem m:
  SLprop.mem_match (full_mem tt ** SLprop.True) m.
Proof.
  eexists (FMem.of_mem m); split. apply FMem.match_of_mem.
  exists (fun p => if Mem.ptr_eq p 0 then UPred.one FCell.emp else UPred.one (Some (m p))),
         (FMem.cell 0 (m 0)).
  splits. 3:split. {
    intro p.
    unfold FMem.cell, FMem.of_mem;
    case Mem.ptr_eq as [[]|]; rewrite !UPred.bind_one;
    constructor.
  }
  exists (fun p => let p := proj1_sig p in FMem.cell p (m p)).
  splits.
  - intros [p] [p'] ->; reflexivity.
  - intro p; cbn.
    case Mem.ptr_eq as [->|]; rewrite UPred.bind_one.
    + apply FCell.JS_None; unfold FMem.cell.
      intros [p' [GE]]; cbn; case Mem.ptr_eq as [<-|]; [exfalso;lia|reflexivity].
    + unshelve eapply FCell.JS_Some with (x := exist _ p _); unfold FMem.cell; cbn.
      * split; cbn; lia.
      * case Mem.ptr_eq as [|]; [reflexivity|congruence].
      * intros [p']; case Mem.ptr_eq as [|]; [left; auto | right; reflexivity].
  - intros [p [GE]].
    exists (m p); cbn; split.
    + unfold NULL; lia.
    + reflexivity.
Qed.

Section Struct.
  Context [A : ptr -> Type] (v : forall p : ptr, Vprop.p (A p))
          {len : nat} {S : Struct v len}.

  Derive make_struct_spec SuchThat (
    VLem SPEC (p : ptr)
    'len' [] [free_range p ~> len'] (len' = Some len)
    '(_ : unit) sel [v p ~> sel] True
    make_struct_spec) As make_struct.
  Proof.
    init_lemma ? ? ->; cbn.
    case S as [->].
    Intro sel; Apply (sel, tt); SL.normalize; reflexivity.
  Qed.

  Derive unmake_struct_spec SuchThat (
    VLem SPEC (p : ptr)
    'sel [] [v p ~> sel] True
    '(_ : unit) tt [free_range p ~> Some len] True
    unmake_struct_spec) As unmake_struct.
  Proof.
    init_lemma ? sel ?; cbn.
    case S as [->].
    Apply sel; reflexivity.
  Qed.
End Struct.

Derive split_full_mem_spec SuchThat (
  VLem SPEC (_ : unit)
  'u [] [full_mem ~> u] True
  '(_ : unit) n [vptr p_next_free ~> n; free_range 2 ~> None] True
  split_full_mem_spec) As split_full_mem.
Proof.
  init_lemma ? ? ?; unfold full_mem; SL.normalize.
  rewrite (split_free_range 1 None 1), free_range_1 by split; cbn.
  unfold free_cell at 1; SL.normalize.
  Intro md0.
  Apply (md0, tt); Apply Logic.I; cbn; SL.normalize.
  reflexivity.
Qed.

Derive intro_malloc_env_spec SuchThat (
  VLem SPEC (n : ptr)
  '(n',len,u) [] [vptr p_next_free ~> n'; free_range n ~> len; vtrue ~> u] (n' = n /\ len = None)
  '(_ : unit) tt [malloc_env ~> tt] True
  intro_malloc_env_spec) As intro_malloc_env.
Proof.
  init_lemma n ((?,?),?) []; subst; unfold malloc_env.
  Apply n; reflexivity.
Qed.

Derive elim_malloc_env_spec SuchThat (
  VLem SPEC (_ : unit)
  'u [] [malloc_env ~> u] True
  '(n : ptr) tt [vptr p_next_free ~> n; free_range n ~> None; vtrue ~> tt] True
  elim_malloc_env_spec) As elim_malloc_env.
Proof.
  init_lemma ? ? ?; reflexivity.
Qed.

Derive split_free_range_spec SuchThat (
  VLem SPEC ((p,n) : ptr * nat)
  'len [] [free_range p ~> len] (le_opt n len)
  '(_ : unit) tt [free_range p ~> Some n; free_range (p + n) ~> option_map (fun m => m - n) len] True
  split_free_range_spec) As v_split_free_range.
Proof.
  init_lemma (p,n) ? ?.
  apply SLprop.eq_imp, split_free_range; auto.
Qed.

End Lemmas.

Section Functions.
  Variable CT : ConcreteProg.context.
  Import VGroup.Tactics VTrue.Tactics.


Definition Init_spec : FDecl SPEC
  (_ : unit)
  'u [] [full_mem ~> u] True
  '(_ : unit) tt [malloc_env ~> tt] True.
Proof. Derived. Defined.
Variable Init : Init_spec CT.

Definition Init_impl : FImpl Init := fun _ =>
  gLem split_full_mem tt;;
  Write p_next_free 2;;
  gLem intro_malloc_env 2.
Lemma Init_correct : FCorrect Init_impl.
Proof. solve_by_wlp. Qed.


Definition Malloc_spec : FDecl SPEC
  (n : nat)
  'u [malloc_env ~> u] [] True
  '(p : ptr) tt [allocated p ~> n; free_range p ~> Some n] True.
Proof. Derived. Defined.
Variable Malloc : Malloc_spec CT.

Definition Malloc_impl : FImpl Malloc := fun n =>
  'g_p <- gLem elim_malloc_env tt;
  'p <- Read p_next_free;
  Write p_next_free (p + n);;
  gRewrite g_p p;;
  gLem v_split_free_range (p, n);;
  gLem intro_malloc_env (p + n);;
  gChange (fun 'tt => ([], [allocated p ~> n]));;
  Ret p.
Lemma Malloc_correct : FCorrect Malloc_impl.
Proof.
  solve_by_wlp.
  - unfold allocated; SL.normalize; reflexivity.
Qed.


Definition Free_spec : FDecl SPEC
  (p : ptr)
  '(u,n,len) [malloc_env ~> u] [allocated p ~> n; free_range p ~> len] (len = Some n)
  '(_ : unit) tt [] True.
Proof. Derived. Defined.
Variable Free : Free_spec CT.

Definition Free_impl : FImpl Free := fun p =>
  'g_p <- gLem elim_malloc_env tt;
  gLem intro_true (vgroup [vtrue ~>; allocated p ~>; free_range p ~>]);;
  gLem intro_malloc_env g_p.
Lemma Free_correct : FCorrect Free_impl.
Proof. solve_by_wlp. Qed.

End Functions.

Definition entries := [
  f_entry Init_spec   Init_correct;
  f_entry Malloc_spec Malloc_correct;
  f_entry Free_spec   Free_correct
].
