Require Import SLFun.Util.
Require Export SLFun.Values.
Require Import SLFun.SL.
Require SLFun.ConcreteProg.

Require Import Coq.Setoids.Setoid.

Module CP := ConcreteProg.
Import SLNotations.
Open Scope slprop.

Definition match_fmem (f : FMem.t) (m : mem) :=
  forall p v, f p = Some v -> m p = v.

Definition mem_match_sl (sl : SLprop.t) (m : mem) :=
  exists fm : FMem.t, match_fmem fm m /\ sl fm.

Lemma mem_match_sl_morph_imp (sl0 sl1 : SLprop.t) (slE : SLprop.imp sl0 sl1) (m : mem):
  mem_match_sl sl0 m -> mem_match_sl sl1 m.
Proof.
  intros (fm & ? & ?); exists fm; auto.
Qed.

Global Add Morphism mem_match_sl
  with signature SLprop.eq ==> eq ==> iff
  as mem_match_sl_morph.
Proof.
  symmetric_iff; intros ? ? slE.
  apply mem_match_sl_morph_imp.
  rewrite slE; reflexivity.
Qed.

Module Spec. Section Spec.
  Local Set Implicit Arguments.
  Variable A : Type.

  Record t := mk {
    pre  : SLprop.t;
    post : A -> SLprop.t;
  }.

  Definition le (s0 s1 : t) :=
    SLprop.imp (pre s1) (pre s0) /\ forall x : A, SLprop.imp (post s0 x) (post s1 x).

  Global Instance le_PreOrder : PreOrder le.
  Proof.
    unfold le. split.
    - intro; split; reflexivity.
    - intros a b c [L0a L0b] [L1a L1b]; split.
      + rewrite L1a, L0a; reflexivity.
      + intro; rewrite L0b, L1b; reflexivity.
  Qed.

  Definition frame (s : t) (fr : SLprop.t) : t := {|
    pre  := pre s ** fr;
    post := fun x => post s x ** fr;
  |}.

  Definition tr (s : t): CP.Spec.t A := {|
    CP.Spec.pre  := mem_match_sl (pre s);
    CP.Spec.post := fun _ r => mem_match_sl (post s r);
  |}.

  Definition wp_match (s : t) (wp : CP.Spec.wp_t A): Prop :=
    forall fr, CP.Spec.wp_impl wp (tr (frame s fr)).

  Definition spec_match (s : t) (t : CP.Spec.t A -> Prop): Prop :=
    forall fr, exists t_s, t t_s /\ CP.Spec.le t_s (tr (frame s fr)).
End Spec. End Spec.

Section F_SPEC.
  Local Set Implicit Arguments.
  Variable sg : CP.f_sig.

  Definition f_spec :=
    CP.f_arg_t sg -> Spec.t (CP.f_ret_t sg) -> Prop.

  Definition match_f_spec (s : f_spec) (t : CP.f_spec sg) : Prop :=
    forall x s_s, s x s_s -> Spec.spec_match s_s (t x).

  Definition tr_f_spec (s : f_spec) : CP.f_spec sg :=
    fun x t_s => exists s_s fr, s x s_s /\ t_s = Spec.tr (Spec.frame s_s fr).

  Lemma tr_f_spec_match (s : f_spec):
    match_f_spec s (tr_f_spec s).
  Proof.
    intros x s_s S fr; do 2 esplit.
    - exists s_s, fr; eauto.
    - reflexivity.
  Qed.
End F_SPEC.

Section SLS.
  Context [SG : CP.sig_context] (SPC : CP.spec_context SG).

  (* Separation Logic Spec *)
  Definition sls [A] (i : CP.instr A) (s : Spec.t A) :=
    Spec.wp_match s (CP.wlp SPC i).

  (* Constructors *)

  Section Ret.
    Context [A : Type] (x : A) (sp : A -> SLprop.t).

    Definition ret_spec : Spec.t A := {|
      Spec.pre  := sp x;
      Spec.post := sp;
    |}.
    
    Lemma Ret : sls (CP.Ret x) ret_spec.
    Proof.
      intros fr m0; simpl; auto.
    Qed.
  End Ret. 
  Section Bind.
    Context [A B : Type]
      [pre : SLprop.t] [itm : A -> SLprop.t] [post : B -> SLprop.t]
      [f : CP.instr A] [g : forall x : A, CP.instr B]
      (Sf : sls f (Spec.mk pre itm)) (Sg : forall x : A, sls (g x) (Spec.mk (itm x) post)).

    Lemma Bind : sls (CP.Bind f (fun x => g x)) (Spec.mk pre post).
    Proof.
      intros fr m0; simpl; intros M0.
      eapply CP.wlp_monotone, Sf, M0.
      simpl; intros x.
      apply (Sg x).
    Qed.
  End Bind.
  Section Call.
    Context [sg : CP.f_sig] (f : CP.fid) (x : CP.f_arg_t sg) (s : Spec.t (CP.f_ret_t sg)).
    Record fun_has_spec : Prop := {
      fd_SIG  : SG f = Some sg;
      fg_SPEC : Spec.spec_match s (CP.fun_has_spec SPC f fd_SIG x);
    }.
    Variables (fs : fun_has_spec).

    Lemma Call : sls (CP.Call f (fd_SIG fs) x) s.
    Proof.
      intros fr m0; simpl; intro M0.
      case fs as [SIG SPEC]; simpl.
      case (SPEC fr) as (t_s & HS & SLE).
      exists t_s. split. exact HS.
      exact (SLE _ M0).
    Qed.
  End Call.
  Section Frame.
    Context [A : Type] (f : CP.instr A) [s : Spec.t A] (Sf : sls f s) (fr : SLprop.t).

    Lemma Frame : sls f (Spec.frame s fr).
    Proof.
      intros fr' m0; simpl.
      setoid_rewrite SLprop.star_assoc at 1.
      intros M0; eapply CP.wlp_monotone, Sf with (fr := (fr ** fr')); auto.
      simpl; setoid_rewrite SLprop.star_assoc; auto.
    Qed.
  End Frame.
  Section Cons. 
    Context [A : Type] (f : CP.instr A) [s0 s1 : Spec.t A] (Sf : sls f s0) (LE : Spec.le s0 s1).

    Lemma Cons : sls f s1.
    Proof.
      intros fr m0; simpl; intro M0.
      eapply CP.wlp_monotone, Sf with (fr := fr); cycle 1; simpl.
      - eapply mem_match_sl_morph_imp, M0.
        apply SLprop.star_morph_imp; [apply LE|reflexivity].
      - intros x m1.
        apply mem_match_sl_morph_imp, SLprop.star_morph_imp; [apply LE|reflexivity].
    Qed.
  End Cons.
  Section Assert.
    Variable (P : SLprop.t).

    Definition sl_assert : @CP.instr SG unit :=
      CP.Assert (fun m => exists fr, mem_match_sl (P ** fr) m).

    Definition assert_spec : Spec.t unit :=
      Spec.mk P (fun _ => P).

    Lemma Assert : sls sl_assert assert_spec.
    Proof.
      intros fr m; simpl; eauto.
    Qed.
  End Assert.
  Section Read.
    Variables (p : ptr) (d : memdata).

    Definition read_spec : Spec.t memdata := {|
      Spec.pre  := SLprop.cell p d;
      Spec.post := fun r => SLprop.cell p d ** SLprop.pure (r = d);
    |}.

    Lemma Read : sls (CP.Read p) read_spec.
    Proof.
      intros fr m; simpl; intro M0.
      setoid_rewrite SLprop.star_comm at 2.
      setoid_rewrite SLprop.star_assoc.
      case M0 as (fm & FM & M0).
      do 2 esplit. exact FM.
      exists FMem.emp, fm; intuition.
      - apply FMem.is_join_emp_r; reflexivity.
      - split. reflexivity.
        apply FM.
        case M0 as (fm_cell & fm_frame & JOIN & CELL & _).
        simpl in CELL; rewrite CELL in JOIN.
        specialize (JOIN p); unfold FMem.cell in JOIN.
        case Mem.ptr_eq in JOIN. 2:congruence.
        case fm_frame in JOIN; simpl in JOIN; congruence.
    Qed.
  End Read.
  Section Write.
    Variables (p : ptr) (d0 d1 : memdata).

    Definition write_spec : Spec.t unit := {|
      Spec.pre  := SLprop.cell p d0;
      Spec.post := fun _ => SLprop.cell p d1;
    |}.

    Lemma Write : sls (CP.Write p d1) write_spec.
    Proof.
      intros fr m; simpl; intros (fm0 & FM0 & fm_0 & fm_f & J0 & C0 & F0).
      simpl in C0; rewrite C0 in J0; clear C0 fm_0.
      exists (fset Mem.ptr_eq p (Some d1) fm0).
      simpl; split.
      - intros q d; unfold Mem.write, fset.
        destruct Mem.ptr_eq. congruence. apply FM0.
      - exists (FMem.cell p d1), fm_f; intuition.
        intro q; generalize (J0 q).
        unfold FMem.cell, fset; case Mem.ptr_eq as [|]; auto.
        destruct fm_f; simpl; [discriminate 1|reflexivity].
    Qed.
  End Write.
End SLS.
