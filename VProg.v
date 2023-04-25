Require Import SLFun.Util SLFun.Values SLFun.SL.
Require SLFun.ConcreteProg SLFun.SLProg SLFun.FunProg.

Require Import Coq.Lists.List.

Import SLNotations.
Import ListNotations.


Module Vprop.
  Record t := mk {
    ty : Type;
    sl : ty -> SLprop.t;
  }.
  Global Arguments mk [ty].
End Vprop.

Module CTX.
  Definition atom := {v : Vprop.t & Vprop.ty v}.

  Definition mka [A : Type] (arg : (A -> SLprop.t) * A) : atom :=
    let (sl, x) := arg in
    existT Vprop.ty (Vprop.mk sl) x.

  Definition sla (a : atom): SLprop.t :=
    Vprop.sl (projT1 a) (projT2 a).

  Definition t := list atom.

  Definition sl : t -> SLprop.t :=
    List.fold_right (fun a => SLprop.star (sla a)) SLprop.emp.

  Definition app : t -> t -> t := @List.app atom.

  Lemma sl_app (c0 c1 : t):
    SLprop.eq (sl (app c0 c1)) (sl c0 ** sl c1).
  Proof.
    induction c0; simpl; SLprop.normalize; [|rewrite IHc0]; reflexivity.
  Qed.

  Module Sub.
    Definition t (c : CTX.t) := Vector.t bool (List.length c).

    Fixpoint sub (c : CTX.t) : t c -> CTX.t :=
      match c with
      | nil     => fun _ => nil
      | x :: xs => fun s =>
          let (hd, tl) := Vector.uncons s in
          let ys := sub xs tl in
          if hd then x :: ys else ys
      end.

    Definition const (c : CTX.t) (v : bool) : t c :=
      Vector.const v (List.length c).
  
    Lemma sub_const_true c:
      sub c (Sub.const c true) = c.
    Proof.
      induction c; simpl; f_equal; auto.
    Qed.
    
    Lemma sub_const_false c:
      sub c (Sub.const c false) = nil.
    Proof.
      induction c; simpl; f_equal; auto.
    Qed.

    Definition neg [c : CTX.t] : t c -> t c :=
      Vector.map negb.

    Definition or [c : CTX.t] : t c -> t c -> t c :=
      Vector.map2 orb.
    
    Definition and [c : CTX.t] : t c -> t c -> t c :=
      Vector.map2 andb.

    Definition minus [c : CTX.t] : t c -> t c -> t c :=
      Vector.map2 (fun b0 b1 => andb b0 (negb b1)).

    Fixpoint app [c0 c1 : CTX.t] : forall (s0 : t c0) (s1 : t c1), t (c0 ++ c1).
    Proof.
      case c0 as [|hd c0].
      - intros _ s1. exact s1.
      - intros s0 s1.
        case s0 as [hd0 tl0] using Vector.caseS'.
        constructor.
        + exact hd0.
        + exact (app c0 c1 tl0 s1).
    Defined.

    Lemma sub_app [c0 c1] (s0 : t c0) (s1 : t c1):
      sub (c0 ++ c1) (app s0 s1) = sub c0 s0 ++ sub c1 s1.
    Proof.
      induction c0.
      - reflexivity.
      - destruct s0 as [[]] using Vector.caseS';
        simpl; f_equal; apply IHc0.
    Qed.

    Lemma map_app [c0 c1] (s0 : t c0) (s1 : t c1) f:
      Vector.map f (app s0 s1) = app (Vector.map f s0) (Vector.map f s1).
    Proof.
      induction c0.
      - reflexivity.
      - destruct s0 using Vector.caseS'.
        simpl; f_equal; apply IHc0.
    Qed.

    Lemma map2_app [c0 c1] (a0 b0 : t c0) (a1 b1 : t c1) f:
      Vector.map2 f (app a0 a1) (app b0 b1) = app (Vector.map2 f a0 b0) (Vector.map2 f a1 b1).
    Proof.
      induction c0.
      - reflexivity.
      - destruct a0 using Vector.caseS'.
        destruct b0 using Vector.caseS'.
        simpl; f_equal; apply IHc0.
    Qed.

    Fixpoint split (c0 c1 : CTX.t) : forall (s : t (c0 ++ c1)), t c0 * t c1.
    Proof.
      case c0 as [|? c0].
      - intro s; split. constructor. exact s.
      - intros [hd tl]%Vector.uncons.
        case (split c0 c1 tl) as (s0, s1).
        exact (Vector.cons _ hd _ s0, s1).
    Defined.
  
    Lemma app_split (c0 c1 : CTX.t) (s : Sub.t (c0 ++ c1)):
      let s01 := Sub.split c0 c1 s in
      s = Sub.app (fst s01) (snd s01).
    Proof.
      induction c0.
      - reflexivity.
      - case s as [hd tl] using Vector.caseS'; simpl.
        specialize (IHc0 tl).
        destruct Sub.split; simpl in *.
        rewrite IHc0; reflexivity.
    Qed.

    Lemma split_app (c0 c1 : CTX.t) (s0 : t c0) (s1 : t c1):
      split c0 c1 (app s0 s1) = (s0, s1).
    Proof.
      induction c0.
      - destruct s0 using Vector.case0. reflexivity.
      - destruct s0 as [? s0] using Vector.caseS'; simpl.
        rewrite (IHc0 s0); reflexivity.
    Qed.


    Fixpoint push [c : CTX.t] : forall (s0 : t c), t c -> t (sub c s0).
    Proof.
      case c as [|c0 c].
      - intros ? _; apply Vector.nil.
      - intro s0.
        case s0 as [hd0 tl0] using Vector.caseS'.
        intros [hd1 tl1]%Vector.uncons.
        pose (tl2 := @push c tl0 tl1).
        case hd0; simpl.
        + exact (Vector.cons _ hd1 _ tl2).
        + exact tl2.
    Defined.

    Lemma push_map [c] (s0 s1 : t c) f:
      push s0 (Vector.map f s1) = Vector.map f (push s0 s1).
    Proof.
      induction c; simpl.
      - reflexivity.
      - destruct s0 as [h ?] using Vector.caseS'; destruct s1 using Vector.caseS'; simpl.
        rewrite IHc.
        case h; reflexivity.
    Qed.

    Lemma sub_push [c] (s0 s1 : t c):
      sub (sub c s0) (push s0 s1) = sub c (and s0 s1).
    Proof.
      induction c; simpl.
      - reflexivity.
      - destruct s0 as [h0 ?] using Vector.caseS'; destruct s1 using Vector.caseS'; simpl.
        case h0; simpl; rewrite IHc; reflexivity.
    Qed.
    
    Fixpoint pull [c : CTX.t] : forall (s0 : t c), t (sub c s0) -> t (sub c (neg s0)) -> t c.
    Proof.
      case c as [|c0 c].
      - intros ? _ _; apply Vector.nil.
      - intro s0.
        case s0 as [hd0 tl0] using Vector.caseS'.
        case hd0; simpl.
        + intros [hd1 tl1]%Vector.uncons s2.
          exact (Vector.cons _ hd1 _ (pull c tl0 tl1 s2)).
        + intros s1 [hd2 tl2]%Vector.uncons.
          exact (Vector.cons _ hd2 _ (pull c tl0 s1 tl2)).
    Defined.

    Lemma map_pull c s0 s1 s2 f:
      Vector.map f (@pull c s0 s1 s2) = pull s0 (Vector.map f s1) (Vector.map f s2).
    Proof.
      induction c as [|c0 c].
      - reflexivity.
      - case s0 as [[] s0] using Vector.caseS'.
        + case s1 as [] using Vector.caseS'; simpl; f_equal; apply IHc.
        + case s2 as [] using Vector.caseS'; simpl; f_equal; apply IHc.
    Qed.

    Lemma sl_pull c s0 s1 s2:
      SLprop.eq (sl (sub c (pull s0 s1 s2)))
                (sl (sub (sub c s0) s1) ** sl (sub (sub c (neg s0)) s2)).
    Proof.
      induction c as [|c0 c].
      - simpl; SLprop.normalize; reflexivity.
      - case s0 as [[] s0] using Vector.caseS'.
        + case s1 as [[]] using Vector.caseS'; simpl;
            rewrite IHc; SLprop.normalize; reflexivity.
        + case s2 as [[]] using Vector.caseS'; simpl;
            rewrite IHc; SLprop.normalize; [rewrite SLprop.star_comm12|]; reflexivity.
    Qed.
  End Sub.

  Definition sub : forall c : t, Sub.t c -> t := Sub.sub.

  Lemma sl_split (c : t) (s : Sub.t c):
    SLprop.eq (sl c) (sl (sub c s) ** sl (sub c (Sub.neg s))).
  Proof.
    induction c; simpl.
    - SLprop.normalize; reflexivity.
    - case s as [hd tl] using Vector.caseS'; simpl.
      rewrite (IHc tl).
      case hd; simpl; SLprop.normalize.
      + reflexivity.
      + apply SLprop.star_comm12.
  Qed.

  Module Inj.
    Inductive ieq (c0 c1 : CTX.t) (img : Sub.t c1) :=
      ieqI (E : SLprop.eq (sl (sub c1 img)) (sl c0)).

    Lemma ieqE [c0 c1 img] (IEQ : ieq c0 c1 img):
      SLprop.eq (sl (sub c1 img)) (sl c0).
    Proof.
      case IEQ; auto.
    Qed.

    (* Tactic to build an [ieq].
       We solve goals of the form:

         ieq [mka vp0 ?sel0 ; ... ; mka vp9 ?sel5 ]
             [mka vp0' sel0'; ... ; mka vp9' sel9']
             ?img

       and instantiate [?sel0]...[?sel5] and [?img] in the process.
       To do so, we find an ordered subset of [c1] with matches [c0].
    *)

    (* An ordered subset is described by associating an index (order) to the elements of the subset. *)
    Definition osub (c1 : CTX.t) := Vector.t (option nat) (length c1).

    Fixpoint n_insert (n : nat) (x : atom) (xs : list (nat * atom)) : list (nat * atom) :=
      match xs with
      | nil => [(n, x)]
      | (n', x') :: tl => if Nat.leb n n' then (n, x) :: xs
                          else (n', x') :: n_insert n x tl
      end.

    Lemma n_insert_eq n x xs:
      SLprop.eq (sl (map snd (n_insert n x xs))) (sla x ** sl (map snd xs)).
    Proof.
      revert n x; induction xs as [|(n', x') tl]; intros; simpl.
      - reflexivity.
      - case Nat.leb; simpl.
        + reflexivity.
        + rewrite IHtl, SLprop.star_comm12; reflexivity.
    Qed.

    Fixpoint n_list_of_osub (c1 : CTX.t) : osub c1 -> list (nat * atom).
    Proof.
      case c1 as [|a c1].
      - intros _. exact nil.
      - intros [[n|] sb]%Vector.uncons.
        + exact (n_insert n a (n_list_of_osub c1 sb)).
        + exact (n_list_of_osub c1 sb).
    Defined.

    (* [c0 : CTX.t] and [img] associated to an ordered subset. *)
    Definition c0_of_osub (c1 : CTX.t) (sb : osub c1) : CTX.t :=
      map snd (n_list_of_osub c1 sb).

    Global Arguments c0_of_osub _ !_/.

    Definition img_of_osub (c1 : CTX.t) : osub c1 -> Sub.t c1 :=
      Vector.map (fun o => match o with Some _ => true | None => false end).

    (* By construction, the [ieq] relation is satisfied. *)
    Lemma osub_ieq (c1 : CTX.t) (sb : osub c1):
      ieq (c0_of_osub c1 sb) c1 (img_of_osub c1 sb).
    Proof.
      constructor; induction c1.
      - simpl; reflexivity.
      - case sb as [[]] using Vector.caseS'; simpl.
        + rewrite n_insert_eq.
          apply SLprop.star_morph_eq. reflexivity.
          apply IHc1.
        + apply IHc1.
    Qed.

    (* To find an ordered subset of [c1] that matches [c0], we generate a dummy goal:

         H9 : ieq_asm (mka vp9' sel9') ?n9
           ...
         H0 : ieq_asm (mka vp0' sel0') ?n0
         =================================
         ieq_goal k [mka vp0 ?sel0; ... ; mka vp5 ?sel5]

       We than consider the elements of [c0] in sequence.
       For each atom [mka vp_i ?sel_i], we find a matching [ieq_asm (mka vp_j' sel_j') ?n_j]
       (with [vp_j' = vp_i]).
       We set [?sel_i] to [sel_j'] and [?n_j] to the current position [k] in [c0].
       We pop [mka vp_i _] from [c0], removes [ieq_asm (mka vp_j' sel_j') _] from the hypotheses,
       increments [k] and continue with the next atom of [c0].
       When [c0] becomes empty, we assign [None] to all remaining [ieq_asm].
     *)

    Inductive ieq_asm (a : atom) (n : option nat): Prop :=.

    Local Lemma inst_ieq_asm a : ieq_asm a None -> unit.
    Proof. constructor. Qed.

    Global Ltac clear_ieq_asm :=
      repeat lazymatch goal with
      | H : ieq_asm _ ?n |- _ => apply inst_ieq_asm in H; clear H
      end.

    Inductive ieq_goal : forall (n : nat) (c0 : CTX.t), Prop :=
      | Ieq_Done n : ieq_goal n nil
      | Ieq_Cons [n a c0] (A : ieq_asm a (Some n)) (C : ieq_goal (S n) c0) : ieq_goal n (a :: c0).

    (* NOTE: we reverse the order of [c1] so that the most recent hypotheses (which are chosen by the
       [match] in case of multiple possibilities) are the leftmost atoms. *)
    Fixpoint ieq_unification_goal_aux (TRG : Prop) (c1 : CTX.t): forall (sb : osub c1), Prop.
    Proof.
      case c1 as [|a c1].
      - intros _; exact TRG.
      - intros [n sb]%Vector.uncons.
        exact (ieq_unification_goal_aux (ieq_asm a n -> TRG) c1 sb).
    Defined.
    
    Definition ieq_unification_goal (c0 c1 : CTX.t) (sb : osub c1): Prop :=
      ieq_unification_goal_aux (ieq_goal O c0) c1 sb.

    Lemma ieqI_osub [c0 c1 : CTX.t]
      (sb : osub c1)
      (U : ieq_unification_goal c0 c1 sb)
      (C0 : c0 = c0_of_osub c1 sb)
      [img : Sub.t c1] (IMG : img = img_of_osub c1 sb):
      ieq c0 c1 img.
    Proof.
      subst; apply osub_ieq.
    Qed.

    Global Ltac build :=
      simple refine (CTX.Inj.ieqI_osub _ _ _ _);
      [ (* sb *)
        Vector.build_shape
      | (* U *)
        clear; cbn; intros;
        repeat lazymatch goal with
          | H : CTX.Inj.ieq_asm (existT _ ?v _) _ |- CTX.Inj.ieq_goal _ (existT _ ?v _ :: _) =>
              refine (Ieq_Cons H _); clear H
          | |- ieq_goal _ nil =>
              clear_ieq_asm; exact (Ieq_Done _)
          | |- ieq_goal _ (existT _ ?v _ :: _) =>
              fail "Inj.build" v
        end
      | (* C0  *) cbn; reflexivity
      | (* IMG *) cbn; reflexivity ].
  End Inj.
End CTX.

Module VpropList.
  Definition t := list Vprop.t.

  Definition sel : t -> list Type := map Vprop.ty.
  Definition sel_t (vs : t) := Tuple.t (sel vs).

  Fixpoint inst (vs : t) {struct vs} : sel_t vs -> CTX.t :=
    match vs with
    | nil     => fun _ => nil
    | v :: vs => fun '(sel, sels) => existT _ v sel :: inst vs sels
    end.

  Definition of_ctx : CTX.t -> t :=
    map (@projT1 _ _).

  Lemma of_inst (vs : t) (sl : sel_t vs):
    of_ctx (inst vs sl) = vs.
  Proof.
    induction vs; simpl.
    - reflexivity.
    - destruct sl; simpl; f_equal; auto.
  Defined.

  Fixpoint sel_of_ctx (c : CTX.t) : sel_t (of_ctx c) :=
    match c with
    | nil => tt
    | existT _ v s :: c => (s, sel_of_ctx c)
    end.

  Lemma inst_of_ctx ctx:
    inst (of_ctx ctx) (sel_of_ctx ctx) = ctx.
  Proof.
    induction ctx as [|[]]; simpl; f_equal; auto.
  Qed.

  Fixpoint app_sel [vs0 vs1 : t] (ss0 : sel_t vs0) (ss1 : sel_t vs1) : sel_t (vs0 ++ vs1) :=
    match vs0 as vs0 return sel_t vs0 -> sel_t (vs0 ++ vs1) with
    | nil       => fun _ => ss1
    | v0 :: vs0 => fun '(s0, ss0) => (s0, app_sel ss0 ss1)
    end ss0.
  
  Lemma inst_app vs0 vs1 ss0 ss1:
    inst (vs0 ++ vs1) (app_sel ss0 ss1) = inst vs0 ss0 ++ inst vs1 ss1.
  Proof.
    induction vs0; simpl.
    - reflexivity.
    - case ss0 as (s0, ss0); simpl.
      rewrite IHvs0; reflexivity.
  Qed.

  Definition app_of_ctx c0 c1:
    VpropList.of_ctx (c0 ++ c1) = VpropList.of_ctx c0 ++ VpropList.of_ctx c1
    := ListTransp.map_app _ c0 c1.
End VpropList.

Module _Abbrev.
  Module CP  := SLFun.ConcreteProg.
  Module SP  := SLFun.SLProg.
  Module FP  := SLFun.FunProg.
  Module TF  := FP.TF.
  Module Sub := CTX.Sub.
End _Abbrev.
Import _Abbrev.

Module Spec.
Section Spec.
  Local Set Implicit Arguments.
  Variable A : Type.

  Record t_r3 (vp : VpropList.t) : Type := mk_r3 {
    spost : VpropList.sel_t vp; (* post condition selectors *)
    ens   : Prop;               (* ensures *)
  }.

  Record t_r2 : Type := mk_r2 {
    sel1_t : list Type;
    vpost  : VpropList.t; (* post condition vprops *)
    f_r3 :> Tuple.t sel1_t -> t_r3 vpost; (* TODO? arrow *)
  }.

  Record t_r1 : Type := mk_r1 {
    prs : CTX.t; (* preserved *)
    pre : CTX.t; (* pre condition *)
    req : Prop;  (* requires *)
    f_r2 :> A -> t_r2;
  }.

  Record t : Type := mk_r0 {
    sel0_t : Type;
    f_r1 :> sel0_t -> t_r1;
  }.

  Definition post (vp : VpropList.t) (s : t_r3 vp) : CTX.t :=
    VpropList.inst vp (spost s).

End Spec.
Module Expanded. Section Expanded.
  Local Set Implicit Arguments.
  Variable A : Type.

  Record t_r3 : Type := mk_r3 {
    post : CTX.t;
    ens  : Prop;
  }.

  Record t_r2 : Type := mk_r2 {
    sel1_t : Type;
    f_r3 :> sel1_t -> t_r3;
  }.

  Record t_r1 : Type := mk_r1 {
    prs : CTX.t;
    pre : CTX.t;
    req : Prop;
    f_r2 :> A -> t_r2;
  }.

  Record t : Type := mk_r0 {
    sel0_t : Type;
    f_r1 :> sel0_t -> t_r1;
  }.


  Definition tr_post (e : Expanded.t_r2) : SLprop.t :=
    SLprop.ex (sel1_t e) (fun sel1 =>
      SLprop.pure (ens (e sel1)) **
      CTX.sl (post (e sel1)))%slprop.

  Definition tr (vs : t) (ss : SP.Spec.t A) : Prop :=
    exists sel0 : sel0_t vs,
    SP.Spec.eq ss
    {|
      SP.Spec.pre  := SLprop.pure (req (vs sel0)) **
                      CTX.sl (pre (vs sel0)) **
                      CTX.sl (prs (vs sel0));
      SP.Spec.post := fun x : A =>
                      tr_post (vs sel0 x) **
                      CTX.sl (prs (vs sel0));
    |}%slprop.


  Definition to_expanded2 (s : Spec.t_r2) : Expanded.t_r2 :=
    @mk_r2 (Tuple.t (Spec.sel1_t s)) (fun sel1 =>
    mk_r3 (Spec.post (s sel1)) (Spec.ens (s sel1))).

  Definition to_expanded (s : Spec.t A) : Expanded.t :=
    @mk_r0 (Spec.sel0_t s) (fun sel0 =>
    mk_r1 (Spec.prs (s sel0)) (Spec.pre (s sel0)) (Spec.req (s sel0)) (fun x =>
    to_expanded2 (s sel0 x))).

  Inductive of_expanded3 (e : Expanded.t_r3) : Spec.t_r3 (VpropList.of_ctx (post e)) -> Prop
    := of_expanded3I:
    of_expanded3 e (Spec.mk_r3 _ (VpropList.sel_of_ctx (post e)) (ens e)).

  Inductive of_expanded2 (e : Expanded.t_r2) : Spec.t_r2 -> Prop
    := of_expanded2I
    (* changing [sel1_t] into a tuple *)
    (sel1_tu   : list Type)
    (sel1_tu_f : sel1_t e -> Tuple.t sel1_tu)
    (sel1_tu_g : Tuple.t sel1_tu -> sel1_t e)
    (sel1_TU   : Tuple.type_iso_tu (sel1_t e) sel1_tu sel1_tu_f sel1_tu_g)
    (sel1_TU_GOAL : forall sel1 : sel1_t e,
      Tuple.type_iso_tu_goal (e sel1) _ sel1_TU)
    (* the vprops of [post] must be independents of [sel1] *)
    (vpost : VpropList.t)
    (VPOST : Tuple.arrow sel1_tu (fun sel1' =>
      let sel1 : sel1_t e := sel1_tu_g sel1' in
      VpropList.of_ctx (post (e sel1)) = vpost))
    (s3 : Tuple.arrow sel1_tu (fun _ => Spec.t_r3 vpost))
    (S3 : Tuple.arrow sel1_tu (fun sel1' =>
      let sel1 : sel1_t e := sel1_tu_g sel1' in
      of_expanded3 (e sel1)
        (eq_rect_r Spec.t_r3 (Tuple.arrow_to_fun s3 sel1')
                   (Tuple.arrow_to_fun VPOST sel1')))):
    of_expanded2 e (@Spec.mk_r2 sel1_tu vpost (Tuple.arrow_to_fun s3)).

  Inductive of_expanded1 (e : Expanded.t_r1) : Spec.t_r1 A -> Prop
    := of_expanded1I
    (s2 : A -> Spec.t_r2)
    (S2 : forall x : A, of_expanded2 (e x) (s2 x)):
    of_expanded1 e (Spec.mk_r1 (prs e) (pre e) (req e) s2).

  Inductive of_expanded (e : Expanded.t) : Spec.t A -> Prop
    := of_expandedI
    (s1 : sel0_t e -> Spec.t_r1 A)
    (S1 : forall sel0 : sel0_t e, of_expanded1 (e sel0) (s1 sel0)):
    of_expanded e (@Spec.mk_r0 A (sel0_t e) s1).

  Lemma of_expanded2_equiv e s
    (E : of_expanded2 e s):
    SLprop.eq (tr_post e) (tr_post (to_expanded2 s)).
  Proof.
    destruct E; unfold tr_post, to_expanded2; cbn.
    eenough (forall sel1' : Tuple.t sel1_tu, SLprop.eq _ _) as C.
    - apply SLprop.eq_iff_imp; split; cycle 1;
      apply SLprop.imp_exists_l.
      + intro sel1'.
        apply SLprop.imp_exists_r with (wit := sel1_tu_g sel1').
        rewrite (C sel1'). reflexivity.
      + intro sel1.
        apply SLprop.imp_exists_r with (wit := sel1_tu_f sel1).
        rewrite C, (proj1 sel1_TU). reflexivity.
    - intro sel1'.
      apply R_refl. reflexivity.
      set (x_S3 := Tuple.arrow_to_fun S3 sel1'); clearbody x_S3; clear S3.
      set (x_s3 := Tuple.arrow_to_fun s3 sel1') in *.
        simpl in x_s3, x_S3; fold x_s3 in x_S3; clearbody x_s3; clear s3.
      set (x_VPOST := Tuple.arrow_to_fun VPOST sel1') in *; clearbody x_VPOST; clear VPOST.
      destruct x_VPOST; cbn in *.
      case x_S3; cbn.
      rewrite VpropList.inst_of_ctx.
      reflexivity.
  Qed.

  Lemma of_expanded_equiv e s ss
    (E : of_expanded e s):
    tr e ss <-> tr (to_expanded s) ss.
  Proof.
    case E as [s1 S1]; unfold tr; cbn.
    apply Morphisms_Prop.ex_iff_morphism; intro sel0.
    case (S1 sel0) as [s2 S2]; cbn.
    setoid_rewrite (fun x => of_expanded2_equiv (S2 x)).
    reflexivity.
  Qed.
End Expanded. End Expanded.
  
  Definition tr [A : Type] (s : t A) : SP.Spec.t A -> Prop :=
    Expanded.tr (Expanded.to_expanded s).
  
  Definition spec_match [A : Type] (vs : t A) (ss : SP.Spec.t A -> Prop) : Prop :=
    forall s0, tr vs s0 ->
    exists s1, SP.Spec.le s1 s0 /\ ss s1.
End Spec.

Section F_SPEC.
  Local Set Implicit Arguments.
  Variable sg : f_sig.

  Definition f_spec :=
    f_arg_t sg -> Spec.t (f_ret_t sg).

  Definition match_f_spec (vs : f_spec) (ss : SP.f_spec sg) : Prop :=
    forall x, Spec.spec_match (vs x) (ss x).

  Definition tr_f_spec (vs : f_spec) : SP.f_spec sg :=
    fun x => Spec.tr (vs x).

  Lemma tr_f_spec_match (s : f_spec):
    match_f_spec s (tr_f_spec s).
  Proof.
    intros x s0 TR; do 2 esplit.
    - reflexivity.
    - exact TR.
  Qed.

  Record FSpec (e : f_arg_t sg -> Spec.Expanded.t (f_ret_t sg)) := mk_FSpec {
    m_spec  : f_arg_t sg -> Spec.t (f_ret_t sg);
    m_equiv : forall x : f_arg_t sg, Spec.Expanded.of_expanded (e x) (m_spec x);
  }.
End F_SPEC.

Section VProg.

(* [i_spec_t] *)

Local Set Implicit Arguments.
Record i_spec_t (A : Type) (ctx : CTX.t) := mk_i_spec {
  sf_csm  : Sub.t ctx;
  sf_prd  : A -> VpropList.t;
  sf_spec : FP.instr (FP.TF.mk_p A (fun x => VpropList.sel (sf_prd x)));
}.
Local Unset Implicit Arguments.

Definition sf_rsel [A ctx] (s : i_spec_t A ctx) (x : A) : list Type :=
  VpropList.sel (sf_prd s x).
Definition sf_rvar [A ctx] (s : i_spec_t A ctx) : TF.p :=
  TF.mk_p A (sf_rsel s).

Definition sf_post_ctx [A ctx] (s : i_spec_t A ctx) (x : A) (sels : VpropList.sel_t (sf_prd s x)) : CTX.t :=
  VpropList.inst (sf_prd s x) sels ++ CTX.sub ctx (Sub.neg (sf_csm s)).

Definition sf_post [A ctx] (s : i_spec_t A ctx) (post : TF.t (sf_rvar s) -> Prop) (x : A) : SLprop.t :=
  SLprop.ex (VpropList.sel_t (sf_prd s x)) (fun sels =>
    SLprop.pure (post (TF.mk (sf_rsel s) x sels)) **
    CTX.sl (sf_post_ctx s x sels))%slprop.

Global Arguments sf_rvar _ _ !_/.
Global Arguments sf_rsel _ _ !_/.
Global Arguments sf_post _ _ !_ _/.
Global Arguments sf_post_ctx _ _ !_ _ _/.

(* [instr] *)

  Context [SIG : sig_context] (SPC : CP.spec_context SIG).

Definition sound_spec [A : Type] (i : @CP.instr SIG A) (ctx : CTX.t) (s : i_spec_t A ctx) : Prop :=
  forall (post : TF.t (sf_rvar s) -> Prop)
         (PRE : FP.wlp (sf_spec s) post),
  SP.sls SPC i {|
    SP.Spec.pre  := CTX.sl ctx;
    SP.Spec.post := sf_post s post;
  |}.

Definition i_spec_p [A : Type] (i : @CP.instr SIG A) (ctx : CTX.t) : Type :=
  { sp : i_spec_t A ctx -> Prop | forall s (SP : sp s), sound_spec i ctx s }.

Local Set Implicit Arguments.
Record instr (A : Type) := mk_instr {
  i_impl : @CP.instr SIG A;
  i_spec : forall ctx : CTX.t, i_spec_p i_impl ctx;
}.
Local Unset Implicit Arguments.

(* Transformation *)

Section AddCsm.
  Context [A : Type] [ctx : CTX.t] (s : i_spec_t A ctx) (csm : Sub.t ctx).
  
  Let acsm := CTX.sub ctx (Sub.minus csm (sf_csm s)).

  Definition add_csm : i_spec_t A ctx
    :=
    {|
      sf_csm  := Sub.or (sf_csm s) csm;
      sf_prd  := fun x => sf_prd s x ++ VpropList.of_ctx acsm;
      sf_spec := FP.BindA (sf_spec s) (TF.arrow_of_fun (P:=sf_rvar s) (fun x =>
                   FP.Ret (TF.mk _ (TF.v_val x) (VpropList.app_sel (TF.v_sel x) (VpropList.sel_of_ctx acsm)))
                 ))
    |}.

  Local Opaque TF.arrow_to_fun TF.arrow_of_fun.

  Lemma add_csm_sound (i : @CP.instr SIG A):
    sound_spec i ctx s -> sound_spec i ctx add_csm.
  Proof.
    intros S0 post PRE; simpl in PRE.
    eapply SP.Cons.
    apply S0, PRE.
    split; simpl. reflexivity.
    intro x; unfold add_csm, sf_post, sf_post_ctx, sf_rsel; cbn.
    apply SLprop.imp_exists_l; intro sel0.
    apply SLprop.imp_exists_r with (wit := VpropList.app_sel sel0 (VpropList.sel_of_ctx acsm)).
    rewrite TF.arrow_to_of.
    apply SLprop.star_morph_imp. reflexivity.
    rewrite VpropList.inst_app, !CTX.sl_app; SLprop.normalize.
    apply SLprop.star_morph_imp. reflexivity.
    unfold acsm; rewrite VpropList.inst_of_ctx.
    set (c0 := CTX.sub ctx (Sub.neg (sf_csm s))).
    rewrite (CTX.sl_split c0 (Sub.push (Sub.neg (sf_csm s)) csm)).
    unfold Sub.neg, CTX.sub, c0; rewrite <- Sub.push_map with (f := negb).
    rewrite !Sub.sub_push.
    apply R_refl. reflexivity.
    do 3 f_equal; apply Vector.ext; intro k;
      unfold Sub.and, Sub.or, Sub.minus;
      repeat progress (erewrite ?Vector.nth_map2, ?Vector.nth_map by reflexivity).
    - apply Bool.andb_comm.
    - symmetry; apply Bool.negb_orb.
  Qed.
End AddCsm.
Global Arguments add_csm _ _ !_ !_/.

(* Function definition *)

Section FunImpl.
  Context [A : Type] (body : instr A) (spec : Spec.t A).
  Import Spec.

  Definition impl_match :=
    Spec.spec_match spec (SP.sls SPC (i_impl body)).

  Lemma intro_impl_match
    (H : forall sel0 : Spec.sel0_t spec,
         let ctx : CTX.t := Spec.pre (spec sel0) ++ Spec.prs (spec sel0) in
         exists f : i_spec_t A ctx,
         sf_csm f = Sub.const ctx true /\
         sound_spec (i_impl body) ctx f /\
         forall REQ : Spec.req (spec sel0),
         FP.wlp (sf_spec f) (fun r =>
           let x      := TF.v_val r in
           let f_post := VpropList.inst (sf_prd f x) (TF.v_sel r) in
           exists sel1 : Tuple.t (Spec.sel1_t (spec sel0 x)),
           CTX.Inj.ieq (Spec.post (spec sel0 x sel1) ++ Spec.prs (spec sel0))
                       f_post (Sub.const f_post true) /\
           Spec.ens (spec sel0 x sel1)
         )):
    impl_match.
  Proof.
    intros ? [sel0 E].
    setoid_rewrite E; clear E.
    do 2 esplit. reflexivity.
    cbn.
    apply SP.PureE; intro REQ.
    case (H sel0) as (f & F_CSM & F_SPEC & WLP); clear H.
    eapply SP.Cons.
      { apply F_SPEC, WLP, REQ. }
    clear F_SPEC WLP REQ.
    unfold sf_post, sf_post_ctx; split; cbn.
    - rewrite CTX.sl_app; reflexivity.
    - intro x.
      apply SLprop.imp_exists_l; intro rsel.
      apply SLprop.imp_pure_l;   intros (sel1 & ij & ENS).
      unfold Expanded.tr_post; cbn; SLprop.normalize.
      apply SLprop.imp_exists_r with (wit := sel1).
      apply SLprop.imp_pure_r. exact ENS.
      rewrite F_CSM; unfold Sub.neg, Sub.const;
        rewrite Vector.map_const, Sub.sub_const_false, app_nil_r.
      apply CTX.Inj.ieqE in ij; rewrite Sub.sub_const_true, CTX.sl_app in ij.
      rewrite ij; reflexivity.
  Qed.

  Section Impl_Match.
    Variable (s_1 : Spec.t_r1 A).

  Let s_post (x : A) (sel1 : Tuple.t (Spec.sel1_t (s_1 x))) :=
    Spec.post (s_1 x sel1) ++ Spec.prs s_1.
  Let s_vpost (x : A) :=
    Spec.vpost (s_1 x) ++ VpropList.of_ctx (Spec.prs s_1).

  Local Lemma s_vpost_eq (x : A) (sel1 : Tuple.t (Spec.sel1_t (s_1 x))):
    VpropList.of_ctx (s_post x sel1) = s_vpost x.
  Proof.
    unfold s_post, s_vpost, post.
    rewrite VpropList.app_of_ctx, VpropList.of_inst.
    reflexivity.
  Defined.

  Inductive Impl_Match : Prop :=
    Impl_MatchI:
      (* functional representation of the implementation *)
      let ctx : CTX.t := Spec.pre s_1 ++ Spec.prs s_1 in
      forall
      (f0 : i_spec_t A ctx) (F0 : proj1_sig (i_spec body ctx) f0)
      (f  : i_spec_t A ctx) (F  : add_csm f0 (Sub.const ctx true) = f),
      let f_post (r : TF.t (sf_rvar f)) :=
        VpropList.inst (sf_prd f (TF.v_val r)) (TF.v_sel r) in
      forall
      (* simplification of the existential quantification on sel1.
         Maybe we could expend the wlp of add_csm to remove the equalities on
         non consumed vprops ? *)
      (ex_sel1 : forall (x : A) (P : Tuple.t (Spec.sel1_t (s_1 x)) -> Prop),
              Tuple.arrow (VpropList.sel (s_vpost x)) (fun _ => Prop))
      (EX_SEL1 : forall (x : A) (P : Tuple.t (Spec.sel1_t (s_1 x)) -> Prop),
              Tuple.arrow (VpropList.sel (s_vpost x)) (fun rsel =>
              Tuple.ex (sel1_t (s_1 x)) (fun sel1 =>
              Tuple.typed_eq (VpropList.sel_of_ctx (s_post x sel1))
                             (eq_rect_r VpropList.sel_t rsel (s_vpost_eq x sel1)) /\
              P sel1) <-> Tuple.arrow_to_fun (ex_sel1 x P) rsel))

      (* equivalence between the specified post-condition and the post-condition of
         the implementation *)
      (rsel : TF.arrow (sf_rvar f) (fun r => VpropList.sel_t (s_vpost (TF.v_val r))))
      (RSEL : TF.arrow (sf_rvar f) (fun r =>
              CTX.Inj.ieq (VpropList.inst (s_vpost (TF.v_val r)) (TF.arrow_to_fun rsel r))
                          (f_post r) (Sub.const (f_post r) true)))
      (* VC *)
      (WLP : forall REQ : Spec.req s_1,
             FP.wlpA (sf_spec f) (TF.arrow_of_fun (P := sf_rvar f) (fun r =>
               let x := TF.v_val r in
               Tuple.arrow_to_fun (ex_sel1 x (fun sel1 => Spec.ens (s_1 x sel1))) (TF.arrow_to_fun rsel r)))),
      Impl_Match.
  End Impl_Match.

  Lemma intro_impl_match1
    (H : forall sel0, Impl_Match (spec sel0)):
    impl_match.
  Proof.
    apply intro_impl_match.
    intros sel0 ctx.
    destruct (H sel0); clear H.
    exists f. split. 2:split.
    - rewrite <- F; simpl.
      unfold Sub.or, Sub.const; apply Vector.ext.
      intro; erewrite Vector.nth_map2, !Vector.const_nth by reflexivity.
      case Vector.nth in *; reflexivity.
    - rewrite <- F.
      apply add_csm_sound, (proj2_sig (i_spec body ctx)), F0.
    - clear f0 F0 F; intro REQ.
      eapply FP.wlp_monotone, WLP, REQ.
      intro r; rewrite TF.arrow_to_of.
      clear WLP REQ; simpl.
      intros (sel1 & [SEQ] & ENS)%(proj2 (Tuple.arrow_to_fun (EX_SEL1 _ _) _))%Tuple.ex_iff.
      clear ex_sel1 EX_SEL1.
      exists sel1.
      split. 2:exact ENS.
      apply TF.arrow_to_fun with (x := r) in RSEL.
      set (x_VPOST := s_vpost_eq _ _ _) in SEQ; clearbody x_VPOST.
      set (x_rsel  := TF.arrow_to_fun rsel r) in *; clearbody x_rsel; clear rsel; cbn in *.
      set (x_vpost := vpost _ ++ _) in *; clearbody x_vpost.
      destruct x_VPOST; cbn in *; subst x_rsel.
      rewrite VpropList.inst_of_ctx in RSEL.
      exact RSEL.
  Qed.
End FunImpl.

(* Constructors *)

Section Ret.
  Context [A : Type] (x : A) (sp : A -> list Vprop.t).

  Inductive Ret_Spec (ctx : CTX.t) : i_spec_t A ctx -> Prop
    := Ret_SpecI
    (sels : Tuple.t (map Vprop.ty (sp x)))
    (csm : Sub.t ctx)
    (ij : CTX.Inj.ieq (VpropList.inst (sp x) sels) ctx csm) :
    Ret_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := sp;
      sf_spec := FP.Ret (TF.mk (fun x => VpropList.sel (sp x)) x sels);
    |}.

  Program Definition Ret : instr A := {|
    i_impl := CP.Ret x;
    i_spec := fun ctx => Ret_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg csm))).
    - apply SP.Ret
       with (sp := fun x' => (SLprop.pure (x' = x) ** CTX.sl (VpropList.inst (sp x) sels))%slprop).
    - split; simpl.
      + SLprop.normalize. apply SLprop.imp_pure_r. reflexivity.
        rewrite CTX.sl_split with (s := csm).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite (CTX.Inj.ieqE ij); reflexivity.
      + intro x'. SLprop.normalize. apply SLprop.imp_pure_l. intros ->.
        unfold sf_post; cbn.
        apply SLprop.imp_exists_r with (wit := sels).
        apply SLprop.imp_pure_r. assumption.
        rewrite CTX.sl_app. reflexivity.
  Qed.
End Ret.
Section Bind.
  Context [A B : Type] (f : instr A) (g : A -> instr B).
  
  Inductive Bind_Spec (ctx : CTX.t) : i_spec_t B ctx -> Prop
    := Bind_SpecI : forall
    (s_fp : {s_f : i_spec_t A ctx
                 | proj1_sig (i_spec f ctx) s_f}),
    let s_f := proj1_sig s_fp in
    let f_prd x sels :=
      Sub.app (Sub.const (VpropList.inst (sf_prd s_f x) sels) true)
                  (Sub.const (CTX.sub ctx (Sub.neg (sf_csm s_f))) false)
    in forall
    (s_gp : forall (x : A) (sels : VpropList.sel_t (sf_prd s_f x)),
            let ctx1 := sf_post_ctx s_f x sels in
            {s_g : i_spec_t B ctx1
                 | proj1_sig (i_spec (g x) ctx1) s_g}),
    let s_g := fun x sels => add_csm (proj1_sig (s_gp x sels)) (f_prd x sels)
    in forall
    (csm : Sub.t ctx)
    (CSM : forall x sels,
      Sub.pull (sf_csm s_f) (Sub.const _ true) (snd (Sub.split _ _ (sf_csm (s_g x sels))))
      = csm)
    (prd : B -> VpropList.t)
    (PRD : forall x sels, sf_prd (s_g x sels) = prd)
    (spec : FP.instr (TF.mk_p B (fun y => VpropList.sel (prd y))))
    (SPEC : FP.eqv spec (
                let TF_A     := TF.mk_p A (sf_rsel s_f) in
                let TF_B prd := TF.mk_p B (fun y => VpropList.sel (prd y)) in
                @FP.Bind TF_A (TF_B prd)
                    (sf_spec s_f)
                    (fun x =>
                      eq_rect _ (fun prd => FP.instr (TF_B prd))
                                (sf_spec (s_g (TF.v_val x) (TF.v_sel x)))
                                _ (PRD (TF.v_val x) (TF.v_sel x)))
            )),
    Bind_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := prd;
      sf_spec := spec
    |}.
  
  Program Definition Bind : instr B := {|
    i_impl := CP.Bind (i_impl f) (fun x => i_impl (g x));
    i_spec := fun ctx => Bind_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro.
    apply SPEC in PRE; clear SPEC.
    assert (s_g_sound : forall x sels, sound_spec (i_impl (g x)) _ (s_g x sels)).
      { intros; apply add_csm_sound, (proj2_sig (i_spec (g x) _) _ (proj2_sig (s_gp x sels))). }
    assert (s_g_csm : forall x sels, exists csm,
        sf_csm (s_g x sels) = Sub.app (Sub.const _ true) csm). {
      intros; exists (snd (Sub.split _ _ (sf_csm (proj1_sig (s_gp x sels))))).
      unfold s_g, f_prd; simpl; clear.
      rewrite (Sub.app_split _ _ (sf_csm (proj1_sig (s_gp x sels)))) at 1.
      unfold Sub.const, Sub.or.
      etransitivity. apply Sub.map2_app.
      f_equal; apply Vector.ext; intro k;
        erewrite Vector.nth_map2, !Vector.const_nth by reflexivity;
        destruct (Vector.nth _ k); reflexivity.
    }
    clearbody s_g; clear s_gp.
    eapply SP.Bind.
    - apply (proj2_sig (i_spec f ctx) _ (proj2_sig s_fp)).
      simpl in PRE; apply PRE.
    - clear PRE.
      intro x; unfold sf_post; simpl.
      apply SP.ExistsE; intro sels0.
      apply SP.PureE; simpl; intro PRE.
      destruct (PRD x sels0); simpl in PRE.
      eapply SP.Cons.
        { apply s_g_sound, PRE. }
      clear PRE.
      split. reflexivity.
      intro y; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      apply SLprop.imp_exists_l; intro sels1.
      apply SLprop.imp_pure_l; intro POST.
      apply SLprop.imp_exists_r with (wit := sels1).
      apply SLprop.imp_pure_r. exact POST.
      rewrite <- (CSM x sels0).
      ecase s_g_csm as [g_csm E]. unfold sf_post_ctx in *; erewrite E.
      clear.
      rewrite !CTX.sl_app. apply SLprop.star_morph_imp. reflexivity.
      rewrite Sub.split_app; simpl.
      unfold Sub.neg, Sub.const.
      rewrite Sub.map_app, Sub.sub_app, Sub.map_pull, !Vector.map_const; simpl.
      rewrite Sub.sl_pull.
      rewrite !Sub.sub_const_false; simpl; SLprop.normalize; reflexivity.
  Qed.

  Local Arguments TF.arrow_of_fun : simpl never.

  Lemma Bind_SpecI1
    [ctx : CTX.t]
    [s_f : i_spec_t A ctx]
    (S_F : proj1_sig (i_spec f ctx) s_f)
    [f_prd : TF.arrow (sf_rvar s_f) (fun x => Sub.t (sf_post_ctx s_f (TF.v_val x) (TF.v_sel x)))]
    (F_PRD : TF.arrow (sf_rvar s_f) (fun x =>
              Sub.app (Sub.const (VpropList.inst (sf_prd s_f (TF.v_val x)) (TF.v_sel x)) true)
                      (Sub.const (CTX.sub ctx (Sub.neg (sf_csm s_f))) false) =
              TF.arrow_to_fun f_prd x))
    [s_g0 : TF.arrow (sf_rvar s_f) (fun x => i_spec_t B (sf_post_ctx s_f (TF.v_val x) (TF.v_sel x)))]
    (S_G0 : TF.arrow (sf_rvar s_f) (fun x =>
              proj1_sig (i_spec (g (TF.v_val x)) _) (TF.arrow_to_fun s_g0 x)))
    [s_g  : TF.arrow (sf_rvar s_f) (fun x => i_spec_t B (sf_post_ctx s_f (TF.v_val x) (TF.v_sel x)))]
    (S_G  : TF.arrow (sf_rvar s_f) (fun x =>
              add_csm (TF.arrow_to_fun s_g0 x) (TF.arrow_to_fun f_prd x) = TF.arrow_to_fun s_g x))
    [csm  : Sub.t ctx]
    (CSM  : TF.arrow (sf_rvar s_f) (fun x =>
              Sub.pull (sf_csm s_f)
                (Sub.const (Sub.sub ctx (sf_csm s_f)) true)
                (snd (Sub.split (VpropList.inst (sf_prd s_f (TF.v_val x)) (TF.v_sel x))
                                (CTX.sub ctx (Sub.neg (sf_csm s_f))) 
                                (sf_csm (TF.arrow_to_fun s_g x)))) = csm))
    [prd : B -> VpropList.t]
    (PRD : TF.arrow (sf_rvar s_f) (fun x => sf_prd (TF.arrow_to_fun s_g x) = prd))
    [spec : FP.instr (TF.mk_p B (fun y => VpropList.sel (prd y)))]
    (SPEC : spec = 
        let TF_A := sf_rvar s_f in
        let TF_B (prd : B -> VpropList.t) :=
          TF.mk_p B (fun y : B => VpropList.sel (prd y)) in
        FP.BindA (sf_spec s_f)
           (TF.arrow_of_fun (fun x =>
              eq_rect (sf_prd (TF.arrow_to_fun s_g x))
                (fun prd0 : B -> VpropList.t => _Abbrev.FP.instr (TF_B prd0))
                (sf_spec (TF.arrow_to_fun s_g x)) prd
                (TF.arrow_to_fun PRD x)))):
    Bind_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := prd;
      sf_spec := spec;
    |}.
  Proof.
    unshelve refine (Bind_SpecI ctx (exist _ s_f S_F) _ csm _ prd _ spec _).
    - intros x sels.
      exists (TF.arrow_to_fun s_g0 (TF.mk _ x sels)).
      exact  (TF.arrow_to_fun S_G0 (TF.mk _ x sels)).
    - intros x sels; simpl.
      apply TF.arrow_to_fun with (x := TF.mk _ x sels) in CSM as <-.
      rewrite <- (TF.arrow_to_fun PRD   (TF.mk _ x sels)),
              <- (TF.arrow_to_fun S_G   (TF.mk _ x sels)),
              <- (TF.arrow_to_fun F_PRD (TF.mk _ x sels)).
      reflexivity.
    - intros x sels; simpl.
      apply TF.arrow_to_fun with (x := TF.mk _ x sels) in CSM as <-.
      rewrite <- (TF.arrow_to_fun S_G   (TF.mk _ x sels)),
              <- (TF.arrow_to_fun F_PRD (TF.mk _ x sels)).
      reflexivity.
    - unfold FP.eqv; subst spec; simpl; intro.
      clear CSM S_F S_G0.
      apply FP.Spec.wp_morph. apply FP.wlp_monotone.
      intros [val sel]; rewrite TF.arrow_to_of; simpl in *.
      revert post.

      set (x_PRD := Tuple.arrow_to_fun (PRD val) sel).
      simpl in x_PRD; fold x_PRD; clearbody x_PRD; clear PRD.
      case x_PRD; simpl; clear x_PRD.

      set (x_S_G := Tuple.arrow_to_fun (S_G val) sel).
      simpl in x_S_G; fold x_S_G; clearbody x_S_G; clear S_G.
      case x_S_G; clear x_S_G s_g.

      set (x_F_PRD := Tuple.arrow_to_fun (F_PRD val) sel).
      simpl in x_F_PRD; fold x_F_PRD; clearbody x_F_PRD; clear F_PRD.
      case x_F_PRD; clear x_F_PRD f_prd; simpl.

      reflexivity.
  Qed.
End Bind.
Section Assert.
  Context [A : Type] (P : A -> CTX.t * Prop).

  Inductive Assert_Spec (ctx : CTX.t) : i_spec_t unit ctx -> Prop
    := Assert_SpecI
    (p : A)
    (img : Sub.t ctx)
    (ij : CTX.Inj.ieq (fst (P p)) ctx img):
    Assert_Spec ctx {|
      sf_csm  := Sub.const ctx false;
      sf_prd  := fun _ => nil;
      sf_spec := FP.Assert (snd (P p))
    |}.
  
  Program Definition Assert : instr unit := {|
    i_impl := SP.sl_assert (SLprop.ex A (fun p =>
                SLprop.pure (snd (P p)) ** CTX.sl (fst (P p))))%slprop;
    i_spec := fun ctx => Assert_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    case PRE as (PRE & POST).
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg img))).
    - apply SP.Assert_imp with (Q := CTX.sl (fst (P p))).
      apply SLprop.imp_exists_r with (wit := p).
      apply SLprop.imp_pure_r. exact PRE.
      reflexivity.
    - eenough (SLprop.eq (CTX.sl ctx) _) as sl_eq.
      split; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      + rewrite sl_eq; reflexivity.
      + intros []; SLprop.normalize.
        apply SLprop.imp_exists_r with (wit := tt).
        apply SLprop.imp_pure_r. exact POST.
        unfold Sub.neg, Sub.const; rewrite Vector.map_const; simpl.
        rewrite Sub.sub_const_true.
        rewrite sl_eq; reflexivity.
      + rewrite CTX.sl_split with (s := img).
        setoid_rewrite (CTX.Inj.ieqE ij).
        reflexivity.
  Qed.
End Assert.
Section Read.
  Context (p : ptr).

  Inductive Read_Spec (ctx : CTX.t) : i_spec_t memdata ctx -> Prop
    := Read_SpecI
    (d : memdata)
    (img : Sub.t ctx)
    (ij : CTX.Inj.ieq [CTX.mka (SLprop.cell p, d)] ctx img):
    Read_Spec ctx {|
      sf_csm  := Sub.const ctx false;
      sf_prd  := fun _ => nil;
      sf_spec := FP.Ret (TF.mk (fun _ => nil) d tt);
    |}.

  Program Definition Read : instr memdata := {|
    i_impl := CP.Read p;
    i_spec := fun ctx => Read_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg img))).
    - eapply SP.Read with (d := d).
    - eassert (IEq : SLprop.eq _ _). {
        etransitivity. apply (CTX.Inj.ieqE ij).
        simpl; SLprop.normalize.
      }
      split; simpl.
      + rewrite CTX.sl_split with (s := img).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite IEq; reflexivity.
      + intro x'. SLprop.normalize. apply SLprop.imp_pure_l. intros ->.
        unfold sf_post; simpl; SLprop.normalize.
        apply SLprop.imp_exists_r with (wit := tt).
        apply SLprop.imp_pure_r. assumption.
        etransitivity. apply SLprop.star_morph_imp. 2:reflexivity. 
        eapply SLprop.imp_morph. symmetry in IEq; exact IEq. 1,2:reflexivity.
        rewrite <- CTX.sl_split.
        unfold Sub.neg, Sub.const; rewrite Vector.map_const; simpl.
        rewrite Sub.sub_const_true.
        reflexivity.
  Qed.
End Read.
Section Write.
  Context (p : ptr) (d : memdata).

  Inductive Write_Spec (ctx : CTX.t) : i_spec_t unit ctx -> Prop
    := Write_SpecI
    (d0 : memdata)
    (csm : Sub.t ctx)
    (ij : CTX.Inj.ieq [CTX.mka (SLprop.cell p, d0)] ctx csm):
    Write_Spec ctx {|
      sf_csm  := csm;
      sf_prd  := fun _ => [Vprop.mk (SLprop.cell p)];
      sf_spec := FP.Ret (TF.mk (fun _ => [memdata]) tt (d, tt));
    |}.

  Program Definition Write : instr unit := {|
    i_impl := CP.Write p d;
    i_spec := fun ctx => Write_Spec ctx;
  |}.
  Next Obligation.
    destruct SP; do 2 intro; simpl in *.
    eapply SP.CFrame with (fr := CTX.sl (CTX.sub ctx (Sub.neg csm))).
    - eapply SP.Write with (d0 := d0).
    - split; unfold sf_post, sf_post_ctx, sf_rsel; simpl.
      + rewrite CTX.sl_split with (s := csm).
        apply SLprop.star_morph_imp. 2:reflexivity.
        rewrite (CTX.Inj.ieqE ij); simpl; SLprop.normalize; reflexivity.
      + intros []; SLprop.normalize.
        apply SLprop.imp_exists_r with (wit := (d, tt)).
        apply SLprop.imp_pure_r. assumption.
        reflexivity.
  Qed.
End Write.

End VProg.

Module Tac.
  Ltac cbn_refl := cbn; repeat intro; reflexivity.

  (* If [t] is a term with a destructive let [let (...) := ?u in _] as head,
     partially instantiate [?u] by applying the constructor, allowing the let to be reduced. *)
  Ltac build_matched_shape t :=
    lazymatch t with (match ?p with _ => _ end) =>
      let H := fresh "_" in
      unshelve eassert (p = _) as H;
      [ econstructor; shelve | reflexivity | clear H ]
    end.

  Local Lemma ref_arg_unit [A : Type] [P : A -> Type] (f : unit -> A) [f' : A]
    (E : f = fun 'tt => f')
    (C : P f'):
    P (f tt).
  Proof.
    rewrite E; exact C.
  Qed.

  Local Lemma ref_arg_pair [A X Y : Type] [P : A -> Type] (f : X * Y -> A) [f' : Y -> X -> A] [x : X] [y : Y]
    (E : f = fun '(x,y) => f' y x)
    (C : P (f' y x)):
    P (f (x, y)).
  Proof.
    rewrite E; exact C.
  Qed.

  Ltac of_expanded_arg :=
    repeat lazymatch goal with
    | |- _ (let 'tt := ?x in _) (?s _) =>
        destruct x;
        refine (ref_arg_unit s eq_refl _)
    | |- _ (let (_,_) := ?x in _) (?s _) =>
        destruct x;
        refine (ref_arg_pair s eq_refl _)
    end.

  Local Lemma mk_red_FSpec [sg : f_sig] [e : f_arg_t sg -> Spec.Expanded.t (f_ret_t sg)]
    [s0 s1 : f_arg_t sg -> Spec.t (f_ret_t sg)]
    (E : forall x : f_arg_t sg, Spec.Expanded.of_expanded (e x) (s0 x))
    (R : s1 = s0):
    FSpec sg e.
  Proof.
    exists s1.
    rewrite R; exact E.
  Defined.

  (* solves a goal [FSpec sig espec] *)
  Ltac build_FSpec :=
    refine (mk_red_FSpec _ _);
    [ cbn;
      intro (* arg *); of_expanded_arg;
      refine (Spec.Expanded.of_expandedI _ _ _); cbn;
      intro (* sel0 *); of_expanded_arg;
      refine (Spec.Expanded.of_expanded1I _ _ _); cbn;
      intro (* ret *);
      simple refine (Spec.Expanded.of_expanded2I _ _ _ _ _ _);
      [ shelve | shelve | shelve | shelve
      | (* sel1_TU_GOAL *) cbn; intro (* sel1 *); Tuple.build_type_iso_tu
      | shelve | (* S_VPOST *) Tac.cbn_refl
      | shelve | (* S3      *) cbn; repeat intro; refine (Spec.Expanded.of_expanded3I _) ]
    | cbn; reflexivity ].


  Ltac build_Ret :=
    simple refine (@Ret_SpecI _ _ _ _ _ _ _);
    [ Tuple.build_shape | shelve | CTX.Inj.build ].

  Ltac build_Bind_init :=
    simple refine (Bind_SpecI1 _ _ _ _ _ _ _ _ _ _);
    [ shelve | | shelve | | shelve | | shelve |
    | shelve | | shelve | | shelve | ].

  Ltac build_Bind build_f :=
    build_Bind_init;
    [ (* S_F   *) hnf; build_f
    | (* F_PRD *) cbn_refl
    | (* S_G0  *) cbn; repeat intro; build_f
    | (* S_G   *) cbn_refl
    | (* CSM   *) cbn_refl
    | (* PRD   *) cbn_refl
    | (* SPEC  *) cbn_refl ].

  Ltac build_Assert :=
    simple refine (@Assert_SpecI _ _ _ _ _ _);
    [ shelve | shelve |
      cbn;
      (* [p : A] can be a tuple let-matched by [P] *)
      repeat lazymatch goal with |- CTX.Inj.ieq (fst ?x) _ _ =>
        build_matched_shape x; cbn
      end;
      (* ij *)
      CTX.Inj.build ].

  Ltac build_Read :=
    simple refine (@Read_SpecI _ _ _ _ _);
    [ shelve | shelve | (* ij *) CTX.Inj.build ].

  Ltac build_Write :=
    simple refine (@Write_SpecI _ _ _ _ _ _);
    [ shelve | shelve | (* ij *) CTX.Inj.build ].

  Ltac build_spec :=
    let rec build_spec :=
    hnf;
    lazymatch goal with
    | |- Ret_Spec    _ _ _ _ => build_Ret
    | |- Bind_Spec _ _ _ _ _ => build_Bind build_spec
    | |- Assert_Spec   _ _ _ => build_Assert
    | |- Read_Spec     _ _ _ => build_Read
    | |- Write_Spec  _ _ _ _ => build_Write
    end
    in build_spec.

  Local Lemma elim_tuple_eq_conj [TS] [u v : Tuple.t TS] [P Q : Prop]
    (C : elim_and_list_f (List.rev_append (Tuple.eq_list u v) nil) Q):
    (Tuple.typed_eq u v /\ P) -> Q.
  Proof.
    rewrite <- List.rev_alt, elim_and_list, and_list_rev, <- Tuple.eq_iff_list in C.
    intros [[] _]; auto.
  Qed.

  Local Lemma simpl_tuple_eq_conj [TS] [u v : Tuple.t TS] [P Q : Prop] [xs : list Prop]
    (E0 : and_list_eq (Tuple.eq_list u v) xs)
    (E1 : and_list xs = Q):
    (Tuple.typed_eq u v /\ P) <-> (Q /\ P).
  Proof.
    case E1, E0 as [<-].
    rewrite <- Tuple.eq_iff_list.
    split.
    - intros ([] & ?); tauto.
    - repeat split; tauto.
  Qed.

  (* solves a goal [(exists x0...x9, Tuple.typed_eq (x0...x9) u /\ P) <-> ?Q]
     by simplifying the lhs. *)
  Ltac simplify_ex_eq_tuple :=
    etransitivity;
    [ repeat first [
        (* remove an [exists x] if we have an equality [x = _] *)
        etransitivity;
        refine (exists_eq_const _ _ (fun x => _));
        repeat refine (ex_ind (fun x => _));
        refine (elim_tuple_eq_conj _);
        cbn; repeat intro; eassumption
      | (* otherwise, conitinue with the next [exists] *)
        refine (Morphisms_Prop.ex_iff_morphism _ _ (fun x => _))
      ]
    | cbn;
      repeat refine (Morphisms_Prop.ex_iff_morphism _ _ (fun x => _));
      refine (VProg.Tac.simpl_tuple_eq_conj _ _);
      (* remove trivial equalities [x = x] *)
      [ repeat first [ refine (simpl_and_list_r1 eq_refl _)
                     | refine (simpl_and_list_e1 _) ];
        exact simpl_and_list_0
      | cbn; reflexivity ]
    ].

  (* change a goal [impl_match SPEC vprog spec] into a condition [req -> wlp f post] *)
  Ltac build_impl_match :=
    refine (intro_impl_match1 _ _ _ _); cbn;
    (* intro and destruct sel0 *)
    intro;
    repeat lazymatch goal with
    |- Impl_Match _ _ (match ?x with _ => _ end) => destruct x
    end;

    simple refine (@Impl_MatchI _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [ shelve | (* F0      *) cbn; Tac.build_spec
    | shelve | (* F       *) Tac.cbn_refl
    | shelve | (* EX_SEL1 *) cbn; repeat intro; simplify_ex_eq_tuple
    | (* rsel *) cbn; repeat intro; Tuple.build_shape
    | (* RSEL *) cbn; repeat intro; CTX.Inj.build
    | (* WLP  *) ].

End Tac.
