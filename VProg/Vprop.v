From SLFun Require Import Util SL.
Import Util.List.

Import SLNotations ListNotations.


Module Vprop.
  Definition p (ty : Type) := ty -> SLprop.t.

  Record t := mk {
    ty : Type;
    sl : p ty;
  }.
  Global Arguments mk [ty].
End Vprop.

Module CTX.
  Definition atom := {v : Vprop.t & Vprop.ty v}.

  Definition mka [A : Type] (arg : Vprop.p A * A) : atom :=
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
    induction c0; simpl; SL.normalize; [|rewrite IHc0]; reflexivity.
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
      - simpl; SL.normalize; reflexivity.
      - case s0 as [[] s0] using Vector.caseS'.
        + case s1 as [[]] using Vector.caseS'; simpl;
            rewrite IHc; SL.normalize; reflexivity.
        + case s2 as [[]] using Vector.caseS'; simpl;
            rewrite IHc; SL.normalize; [rewrite SLprop.star_comm12|]; reflexivity.
    Qed.
  End Sub.

  Definition sub : forall c : t, Sub.t c -> t := Sub.sub.

  Definition sl_opt (h : SLprop.t) (b : bool) : SLprop.t :=
    if b then h else SLprop.emp.

  Fixpoint sl_sub (c : CTX.t) {struct c} : forall (s : Sub.t c), SLprop.t.
  Proof.
    case c as [|a c].
    - exact (fun _ => SLprop.emp).
    - intros [b s]%Vector.uncons.
      exact (sl_opt (sla a) b ** sl_sub c s)%slprop.
  Defined.

  Lemma sl_sub_eq (c : CTX.t) (s : Sub.t c):
    SLprop.eq (sl (sub c s)) (sl_sub c s).
  Proof.
    induction c as [|a c]; cbn.
    - reflexivity.
    - case s as [hd s] using Vector.caseS'; cbn.
      case hd; cbn; rewrite IHc; SL.normalize; reflexivity.
  Qed.


  Lemma sl_split (c : t) (s : Sub.t c):
    SLprop.eq (sl c) (sl (sub c s) ** sl (sub c (Sub.neg s))).
  Proof.
    induction c; simpl.
    - SL.normalize; reflexivity.
    - case s as [hd tl] using Vector.caseS'; simpl.
      rewrite (IHc tl).
      case hd; simpl; SL.normalize.
      + reflexivity.
      + apply SLprop.star_comm12.
  Qed.

  Section Trf.
    Variable (c0 c1 : CTX.t) (rev_f : Sub.t c1 -> (Sub.t c0 * CTX.t (* rem *))).
    Local Set Implicit Arguments.

    Record trf : Prop := {
      trf_fwd : SLprop.imp (sl c0) (sl c1);
      trf_bwd : forall s1 : Sub.t c1, let r := rev_f s1 in
                SLprop.imp (sl (sub c1 s1)) (sl (sub c0 (fst r)) ** sl (snd r))
    }.
  End Trf.
  Global Arguments trf : clear implicits.

  Module Inj.
    Inductive ieq (c0 c1 : CTX.t) (img : Sub.t c1) :=
      ieqI (E : SLprop.eq (sl (sub c1 img)) (sl c0)).

    Lemma ieqE [c0 c1 img] (IEQ : ieq c0 c1 img):
      SLprop.eq (sl (sub c1 img)) (sl c0).
    Proof. apply IEQ. Qed.

    Definition beq (c0 c1 : CTX.t) :=
      ieq c0 c1 (Sub.const c1 true).

    Lemma beq_iff c0 c1:
      beq c0 c1 <-> SLprop.eq (sl c1) (sl c0).
    Proof.
      etransitivity.
      - split. intros [H]; exact H. intro H; constructor; exact H.
      - rewrite Sub.sub_const_true. reflexivity.
    Qed.

    Lemma beqE [c0 c1] (BEQ : beq c0 c1):
      SLprop.eq (sl c1) (sl c0).
    Proof.
      apply beq_iff, BEQ.
    Qed.

    Definition itrf (c0 c1 : CTX.t) (add : CTX.t) (rev_f : Sub.t (c0 ++ add) -> (Sub.t c1 * CTX.t)) : Prop :=
      trf c1 (c0 ++ add) rev_f.

    (* Tactic to build an [ieq].
       We solve goals of the form:

         ieq [mka vp0 ?sel0 ; ... ; mka vp9 ?sel5 ]
             [mka vp0' sel0'; ... ; mka vp9' sel9']
             ?img

       and instantiate [?sel0]...[?sel5] and [?img] in the process.
       To do so, we find an ordered subset of [c1] that matches [c0].
    *)

    (* An ordered subset is described by associating an index (order) to the elements of the subset. *)
    Definition osub (c1 : CTX.t) := Vector.t (option nat) (length c1).

    Section OSub_IEq.
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
    End OSub_IEq.

    (* Alternatively We can also build a [trf] *)
    Section OSub_Trf.
      Definition nat_opt_le (n0 n1 : option nat) : bool :=
        match n1, n0 with
        | None,    _       => true
        | Some n1, Some n0 => Nat.leb n0 n1
        | Some _,  None    => false
        end.

      Fixpoint trf_insert (n : option nat) (x : atom) (l : list (option nat * atom)) {struct l}:
        { l' : list (option nat * atom) & Sub.t (List.map snd l') -> Sub.t (x :: List.map snd l) }.
      Proof.
        case l as [|(n', x') l].
        - exists [(n,x)].
          exact (fun s => s).
        - case (nat_opt_le n n').
          + exists ((n, x) :: (n', x') :: l).
            exact (fun s => s).
          + case (trf_insert n x l) as [l' f].
            exists ((n', x') :: l').
            intros [b' [b bl]%f%Vector.uncons]%Vector.uncons.
            exact (Vector.cons _ b _ (Vector.cons _ b' _ bl)).
      Defined.

      Lemma trf_insert_correct n x l:
        let '(existT _ l' f) := trf_insert n x l in
        SLprop.eq (sl (x :: map snd l)) (sl (map snd l')) /\
        forall s, SLprop.eq (sl_sub (map snd l') s) (sl_sub (x :: map snd l) (f s)).
      Proof.
        induction l as [|(n', x') l IH]; cbn; [|case nat_opt_le]; cbn.
        1,2:split; reflexivity.
        destruct trf_insert as [l' f]; cbn; split.
        - rewrite <- (proj1 IH); cbn.
          apply SLprop.star_comm12.
        - intro s.
          rewrite (proj2 IH); cbn.
          apply SLprop.star_comm12.
      Qed.

      Fixpoint trf_sort_list (c1 : CTX.t) { struct c1 } :
        forall sb : osub c1,
        { l : list (option nat * atom) & Sub.t (List.map snd l) -> Sub.t c1 }.
      Proof.
        case c1 as [|x c1].
        - exact (fun _ => existT _ nil (fun _ => Vector.nil _)).
        - intros (n, sb)%Vector.uncons.
          case (trf_sort_list c1 sb) as [l0 f0].
          case (trf_insert   n x l0) as [l1 f1].
          exists l1.
          exact (fun s1 => let (b, s0) := Vector.uncons (f1 s1) in Vector.cons _ b _ (f0 s0)).
      Defined.

      Lemma trf_sort_list_correct c1 sb:
        let '(existT _ l' f) := trf_sort_list c1 sb in
        SLprop.eq (sl c1) (sl (map snd l')) /\
        forall s, SLprop.eq (sl_sub (map snd l') s) (sl_sub c1 (f s)).
      Proof.
        induction c1 as [|x c1 IH]; cbn.
        - split; reflexivity.
        - case sb as [n sb] using Vector.caseS'; cbn.
          specialize (IH sb).
          destruct trf_sort_list as [l0 f0].
          specialize (trf_insert_correct n x l0) as IC.
          destruct trf_insert    as [l1 f1].
          split.
          + rewrite <- (proj1 IC); cbn.
            rewrite <- (proj1 IH); reflexivity.
          + intro s; cbn.
            rewrite (proj2 IC); cbn.
            rewrite (proj2 IH); reflexivity.
      Qed.

      Variables (c1 : CTX.t) (sb : osub c1).

      Definition trf_c0_of_osub : CTX.t :=
        List.map snd (projT1 (trf_sort_list c1 sb)).

      Definition trf_rev_f_of_osub (s : Sub.t trf_c0_of_osub) : Sub.t c1 * CTX.t :=
        (projT2 (trf_sort_list c1 sb) s, nil).

      Lemma osub_trf:
        trf c1 trf_c0_of_osub trf_rev_f_of_osub.
      Proof.
        unfold trf_rev_f_of_osub, trf_c0_of_osub.
        specialize (trf_sort_list_correct c1 sb).
        pattern (trf_sort_list c1 sb).
        destruct trf_sort_list as [c0 f]; cbn.
        intros [FWD BWD].
        split.
        - rewrite FWD; reflexivity.
        - intro s; cbn.
          rewrite !sl_sub_eq, BWD.
          SL.normalize.
          reflexivity.
      Qed.
    End OSub_Trf.


    (* To find an ordered subset of [c1] that matches [c0], we generate a dummy goal:

         H9 : ieq_asm (mka vp9' sel9') ?n9
           ...
         H0 : ieq_asm (mka vp0' sel0') ?n0
         ===============================================
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

    (* solves a goal [ieq_unification_goal c0 c1 ?sb] *)
    Ltac build_ieq_unification_goal :=
      clear; cbn; intros;
      repeat lazymatch goal with
      | H : CTX.Inj.ieq_asm (existT _ ?v _) _ |- CTX.Inj.ieq_goal _ (existT _ ?v _ :: _) =>
          refine (Ieq_Cons H _); clear H
      | |- ieq_goal _ nil =>
          clear_ieq_asm; exact (Ieq_Done _)
      | |- ieq_goal _ (existT _ ?v _ :: _) =>
          idtac "FAILURE: Inj.build failed to find" v ". Remaining context:";
          try match goal with
           _ : CTX.Inj.ieq_asm (existT _ ?v0 _) _ |- _ => idtac "-" v0; fail
          end;
          fail 1 "Inj.build" v
      end.

    Local Lemma build_ieq_by_osub [c0 c1 : CTX.t]
      (sb : osub c1)
      (U  : ieq_unification_goal c0 c1 sb)
      (C0 : c0 = c0_of_osub c1 sb)
      [img : Sub.t c1] (IMG : img = img_of_osub c1 sb):
      ieq c0 c1 img.
    Proof.
      subst; apply osub_ieq.
    Qed.

    (* solves a goal [ieq c0 c1 img]
       The selectors of [c0] must be evars.
       [img] can be an evar. *)
    Global Ltac build_ieq :=
      simple refine (build_ieq_by_osub _ _ _ _);
      [ (* sb  *) Vector.build_shape
      | (* U   *) build_ieq_unification_goal  
      | (* C0  *) cbn; reflexivity
      | (* IMG *) cbn; reflexivity ].

    (* This builds an injection then checks that it consumes everything. *)
    Global Ltac build_beq := build_ieq.

    Local Lemma build_itrf_by_osub [c0 c1 : CTX.t]
      (sb : osub c1)
      (U : ieq_unification_goal c0 c1 sb)
      [add : CTX.t] (C0 : c0 ++ add = trf_c0_of_osub c1 sb):
      itrf c0 c1 add (eq_rect_r (fun c0a => Sub.t c0a -> _) (trf_rev_f_of_osub c1 sb) C0).
    Proof.
      unfold itrf.
      specialize (osub_trf c1 sb).
      generalize (trf_rev_f_of_osub c1 sb) as rev_f.
      case C0; cbn.
      auto.
    Qed.

    (* solves a goal [itrf c0 c1 ?add ?rev_f]
       The selectors of [c0] must be evars. *)
    Global Ltac build_itrf :=
      simple refine (build_itrf_by_osub _ _ _);
      [ (* sb *) Vector.build_shape
      | (* U  *) build_ieq_unification_goal
      | (* C0 *) cbn; reflexivity ].

    Section Test.
      Variable v : nat -> Vprop.p nat.

      Goal exists sl0 sl1 add rev_f,
        itrf [mka (v 0, sl0); mka (v 1, sl1)] [mka (v 1, 1); mka (v 2, 2); mka (v 0, 0)]
          add rev_f.
      Proof.
        do 4 eexists. build_itrf.
      Qed.
    End Test.
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
    := List.Transp.map_app _ c0 c1.
End VpropList.

