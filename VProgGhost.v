From SLFun Require Import Util Values SL VProg.
From Coq   Require Import Lists.List.

Import SLNotations SL.Tactics.
Import ListNotations.
Import VProg.Notations.

Section Admit.
  Lemma admit_change {A} : @ghost_lem (mk_f_sig (VpropList.t * (A -> VpropList.t)) A)
    (fun '(V0, V1) _ =>
     Spec.mk_r0 (Tuple.force_match (VpropList.sel V0) (fun sel0 =>
     Spec.mk_r1 (GO := None) [] (VpropList.inst V0 sel0) False (fun x =>
     Spec.mk_r2 _ (V1 x) (Tuple.of_fun (fun sel1 =>
     Spec.mk_r3 _ sel1 True)))))).
  Proof.
    init_lemma (?, ?) ?.
    rewrite Tuple.to_of_fun; intros [].
  Qed.
End Admit.
Section Equivalence.
  Variables (V0 V1 : VpropList.t).
  Section Proof.
    Variables (f : VpropList.sel_t V0 -> VpropList.sel_t V1) (g : VpropList.sel_t V1 -> VpropList.sel_t V0).

    Definition eqv_lem1_spec : ghost_spec (mk_f_sig unit unit) :=
      fun _ _ =>
      Spec.mk_r0 (Tuple.force_match (VpropList.sel V0) (fun sel0 =>
      Spec.mk_r1 [] (VpropList.inst V0 sel0) True (fun _ =>
      Spec.mk_r2 [] V1 (
      Spec.mk_r3 _ (f sel0) True)))).
    
    Definition eqv_lem2_spec : ghost_spec (mk_f_sig unit unit) :=
      fun _ _ =>
      Spec.mk_r0 (Tuple.force_match (VpropList.sel V1) (fun sel1 =>
      Spec.mk_r1 [] (VpropList.inst V1 sel1) True (fun _ =>
      Spec.mk_r2 [] V0 (
      Spec.mk_r3 _ (g sel1) True)))).

    Hypothesis (GF : forall x, g (f x) = x)
               (E : forall y, SLprop.eq (CTX.sl (VpropList.inst V0 (g y))) (CTX.sl (VpropList.inst V1 y))).
 
    Lemma eqv_lem1 : ghost_lem eqv_lem1_spec.
    Proof.
      init_lemma _ sel0 _.
      rewrite Tuple.to_of_fun; cbn; SL.normalize.
      rewrite !CTX.sl_app, <- E, GF.
      reflexivity.
    Qed.
    
    Lemma eqv_lem2 : ghost_lem eqv_lem2_spec.
    Proof.
      init_lemma _ sel1 _.
      rewrite Tuple.to_of_fun; cbn; SL.normalize.
      rewrite !CTX.sl_app, E.
      reflexivity.
    Qed.
  End Proof.

  Variables
    (f : Tuple.arrow (VpropList.sel V0) (fun _ => Tuple.u_t (VpropList.sel V1)))
    (g : Tuple.arrow (VpropList.sel V1) (fun _ => Tuple.u_t (VpropList.sel V0))).

  Let f' x := Tuple.of_u_t (Tuple.to_fun f x).
  Let g' x := Tuple.of_u_t (Tuple.to_fun g x).

  Definition eqv_lemma : Prop :=
    ghost_lem (eqv_lem1_spec f') /\ ghost_lem (eqv_lem2_spec g').

  Lemma intro_eqv_lemma
    (GF : Tuple.arrow (VpropList.sel V0) (fun sel0 => g' (f' sel0) = sel0))
    (E  : Tuple.arrow (VpropList.sel V1) (fun sel1 =>
            SLprop.eq (CTX.sl (VpropList.inst V0 (g' sel1)))
                      (CTX.sl (VpropList.inst V1 sel1))))
    : eqv_lemma.
  Proof.
    specialize (Tuple.to_fun GF) as GF'.
    specialize (Tuple.to_fun  E) as E'.
    split; eauto using eqv_lem1, eqv_lem2.
  Qed.

  Definition gUnfold {SIG SPC} (L : eqv_lemma) : @instr SIG SPC unit :=
    gLem (proj1 L) tt.
  Definition gFold {SIG SPC} (L : eqv_lemma) : @instr SIG SPC unit :=
    gLem (proj2 L) tt.
End Equivalence.
Global Arguments gUnfold [_ _ _ _] {_ _} L.
Global Arguments gFold   [_ _ _ _] {_ _} L.
Section Replace.
  Definition replace1_spec A : LDecl (Vprop.p A * Vprop.p A) unit
    FOR (v0, v1) FOR x [] [v0 ~> x] (v0 = v1)
    RET _ FOR tt [v1 ~> x] True.
  Proof. Derive. Defined.
  Lemma replace1 {A} : replace1_spec A.
  Proof.
    init_lemma (v0, v1) sel0 E; subst; reflexivity.
  Qed.

  Definition replace (V0 V1 : VpropList.t) : @ghost_lem (mk_f_sig (VpropList.sel V0 = VpropList.sel V1) unit)
    (fun E _ =>
     Spec.mk_r0 (Tuple.force_match (VpropList.sel V0) (fun sel0 =>
     Spec.mk_r1 [] (VpropList.inst V0 sel0)
       (eq_rect _ (fun st => Tuple.t st -> CTX.t) (VpropList.inst V0) _ E = VpropList.inst V1) (fun _ =>
     Spec.mk_r2 [] V1 (
     Spec.mk_r3 _ (eq_rect _ Tuple.t sel0 _ E) True))))).
  Proof.
    init_lemma E sel0.
    rewrite Tuple.to_of_fun; cbn.
    intros <-.
    SL.normalize.
    destruct E; cbn; reflexivity.
  Qed.
End Replace.
Section Impp.
  Context [sel_t A : Type] (spc : sel_t -> (CTX.t * Prop * (A -> Prop))).

  Definition impp_lemma_spec : ghost_spec (mk_f_sig unit A) :=
      fun _ _ =>
      Spec.mk_r0 (fun (sel : sel_t) => let '(sl, pre, post) := spc sel in
      Spec.mk_r1 (GO := None) sl [] pre (fun (x : A) =>
      Spec.mk_r2 [] [] (
      Spec.mk_r3 [] tt (post x)))).

  Definition impp_lemma := ghost_lem impp_lemma_spec.

  Lemma intro_impp_lemma
    (H : forall sel : sel_t, let '(sl, pre, post) := spc sel in
         pre -> SLprop.impp (CTX.sl sl) (exists x : A, post x)):
    impp_lemma.
  Proof.
    unfold impp_lemma.
    init_lemma [] sel PRE.
    specialize (H sel).
    destruct (spc sel) as ((sl, pre), post); cbn in *.
    SL.normalize.
    eapply SLprop.cut_pure. apply H, PRE.
    intros [x POST].
    Apply x.
    Apply POST.
    reflexivity.
  Qed.
End Impp.
