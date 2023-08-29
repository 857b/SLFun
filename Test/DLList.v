From SLFun     Require Import Util Values SL VProg.Main.
From SLFun.Lib Require Malloc DLList.

Import Util.List.
Import SLNotations ListNotations VProg.Main.Notations FunProg.Notations.
Import SL.Tactics.

Module DL := SLFun.Lib.DLList.

(* A test instantiation of the doubly linked list library *)

Section Definitions.
  Import DL.Param.

  (* list cell *)

  Definition lcell_t := DL.Param.lcell_t memdata.

  Definition p_data (p : ptr) : ptr := p.
  Definition p_prev (p : ptr) : ptr := S p.
  Definition p_next (p : ptr) : ptr := S (S p).

  Lemma lcell_p (p : ptr):
    VRecord.p lcell_t [vptr (p_data p) ~>; vptr (p_prev p) ~>; vptr (p_next p) ~>]
      (fun v => (data v, prev v, next v))
      (fun dt pr nx => DL.Param.mk_lcell dt pr nx).
  Proof.
    constructor; cbn; reflexivity.
  Qed.

  Definition lcell (p : ptr) : Vprop.p lcell_t := VRecord.v (lcell_p p).
  Global Arguments lcell : simpl never.

  Definition lcell_unfold p sl:
    CTX.Trf.Tac.unfold_rule (lcell p ~> sl) (VRecord.v (lcell_p p) ~> sl).
  Proof.
    reflexivity.
  Qed.

  Global Instance lcell_Struct : Malloc.Struct lcell 3.
  Proof.
    split; intro p.
    do 2 rewrite
        Malloc.split_free_range with (n := 1),
        !Malloc.free_range_1,
        PeanoNat.Nat.add_1_r
      by (cbn; auto).
    unfold Malloc.free_cell, lcell; SL.normalize.
    apply SLprop.eq_iff_imp; split;
      [ Intro v0; Intro v1; Intro v2; Apply (mk_lcell v0 v1 v2)
      | Intro [v0 v1 v2]; Apply v0; Apply v1; Apply v2 ];
      SL.normalize; reflexivity.
  Qed.

  Program Definition vP : DL.Param.vp := {| vcell := lcell |}.
  Next Obligation.
    unfold lcell; SL.normalize.
    eapply SLprop.impp_enough.
    SLprop.split_impp; [apply SLprop.cell_non_null | apply SLprop.impp_True..].
    tauto.
  Qed.

End Definitions.

Section Impl.
  Variable CT : ConcreteProg.context.

  Variables
    (Init   : Malloc.Init_spec   CT)
    (Malloc : Malloc.Malloc_spec CT)
    (Length : DL.Length_spec vP  CT).

  (* Set up automatic intro/elim of vprops *)

  Local Hint Resolve lcell_unfold | 1 (CTX.Trf.Tac.unfold_rule (lcell ?p ~> ?sl) _) : CtxTrfDB.
  (* NOTE: the default pattern does not work when interacting with definitions from [Lib.DLList],
           probably because of a mismatch [lcell_t] versus [DL.Param.lcell_t memdata]. *)
  Import VRecord.Tactics VGroup.Tactics.

  (* implementations needed by the generic doubly linked list library *)
  Definition iP : DL.Param.impl vP CT.
  Proof.
    refine {|
      DL.Param.read_prev  := mkFrag (fun p       => Read (p_prev p));
      DL.Param.write_prev := mkFrag (fun '(p, r) => Write (p_prev p) r);
      DL.Param.read_next  := mkFrag (fun p       => Read (p_next p));
      DL.Param.write_next := mkFrag (fun '(p, r) => Write (p_next p) r);
    |}.
    all:abstract solve_by_wlp.
  Defined.

  Definition Main_spec : FDecl SPEC
    (_ : unit)
    'u [] [Malloc.full_mem ~> u] True
    '(r : nat) tt [vtrue ~> tt] (r = 1).
  Proof. Derived. Defined.
  Variable Main : Main_spec CT.

  Definition Main_impl : FImpl Main := fun _ =>
    Init tt;;
    'p <- Malloc 3;
    gLem (Malloc.make_struct lcell) p;;
    Write (p_prev p) NULL;;
    Write (p_next p) NULL;;
    gLem (DL.intro_lseg_nil  vP) (p, NULL);;
    gLem (DL.intro_lseg_cons vP) (NULL, p, NULL, NULL);;
    'r <- Length p NULL;
    gLem intro_true (vgroup [Malloc.malloc_env ~>; Malloc.allocated p ~>; DL.lseg vP NULL p NULL~>]);;
    Ret r.
  Lemma Main_correct : FCorrect Main_impl.
  Proof.
    solve_by_wlp.
  Qed.

End Impl.

Definition entries := [
  f_entry Main_spec     Main_correct
] ++ Malloc.entries ++ DL.entries vP.

Derive prog SuchThat (ConcreteProg.of_entries entries (aux := [existT _ _ iP]) prog)
  As prog_correct.
Proof. Derived. Qed.
