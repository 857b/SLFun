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

  (* An alias for [ty] that is not reduced in order to keep trace of the vprop *)
  Definition sel := ty.
  Global Arguments sel : simpl never.
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

    Definition nil : t [] := Vector.nil bool.
    Global Arguments nil/.

    Definition cons {a : atom} (hd : bool) {c : CTX.t} (tl : t c) : t (a :: c) :=
      Vector.cons bool hd (length c) tl.
    Global Arguments cons/.

    Definition uncons {a : atom} {c : CTX.t}: t (a :: c) -> bool * t c :=
      @Vector.uncons bool (length c).

    Definition caseS' {a : atom} {c : CTX.t}:
      forall (s : t (a :: c))
             (P : t (a :: c) -> Type)
             (H : forall (h : bool) (t : t c), P (cons h t)),
      P s :=
      Vector.caseS'.

    Definition const (c : CTX.t) (v : bool) : t c :=
      Vector.const v (List.length c).
  
    Lemma sub_const_true c:
      sub c (Sub.const c true) = c.
    Proof.
      induction c; simpl; f_equal; auto.
    Qed.
    
    Lemma sub_const_false c:
      sub c (Sub.const c false) = [].
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
        case s0 as [hd0 tl0] using caseS'.
        constructor.
        + exact hd0.
        + exact (app c0 c1 tl0 s1).
    Defined.

    Lemma sub_app [c0 c1] (s0 : t c0) (s1 : t c1):
      sub (c0 ++ c1) (app s0 s1) = sub c0 s0 ++ sub c1 s1.
    Proof.
      induction c0.
      - reflexivity.
      - destruct s0 as [[]] using caseS';
        simpl; f_equal; apply IHc0.
    Qed.

    Lemma map_app [c0 c1] (s0 : t c0) (s1 : t c1) f:
      Vector.map f (app s0 s1) = app (Vector.map f s0) (Vector.map f s1).
    Proof.
      induction c0.
      - reflexivity.
      - destruct s0 using caseS'.
        simpl; f_equal; apply IHc0.
    Qed.

    Lemma map2_app [c0 c1] (a0 b0 : t c0) (a1 b1 : t c1) f:
      Vector.map2 f (app a0 a1) (app b0 b1) = app (Vector.map2 f a0 b0) (Vector.map2 f a1 b1).
    Proof.
      induction c0.
      - reflexivity.
      - destruct a0 using caseS'.
        destruct b0 using caseS'.
        simpl; f_equal; apply IHc0.
    Qed.

    Fixpoint split (c0 c1 : CTX.t) : forall (s : t (c0 ++ c1)), t c0 * t c1.
    Proof.
      case c0 as [|? c0].
      - intro s; split. constructor. exact s.
      - cbn; intros [hd tl]%uncons.
        case (split c0 c1 tl) as (s0, s1).
        exact (cons hd s0, s1).
    Defined.
  
    Lemma app_split (c0 c1 : CTX.t) (s : Sub.t (c0 ++ c1)):
      let s01 := Sub.split c0 c1 s in
      s = Sub.app (fst s01) (snd s01).
    Proof.
      induction c0.
      - reflexivity.
      - case s as [hd tl] using caseS'; simpl.
        specialize (IHc0 tl).
        destruct Sub.split; simpl in *.
        rewrite IHc0; reflexivity.
    Qed.

    Lemma split_app (c0 c1 : CTX.t) (s0 : t c0) (s1 : t c1):
      split c0 c1 (app s0 s1) = (s0, s1).
    Proof.
      induction c0.
      - destruct s0 using Vector.case0. reflexivity.
      - destruct s0 as [? s0] using caseS'; simpl.
        rewrite (IHc0 s0); reflexivity.
    Qed.


    Fixpoint push [c : CTX.t] : forall (s0 : t c), t c -> t (sub c s0).
    Proof.
      case c as [|c0 c].
      - intros ? _; exact nil.
      - intro s0.
        case s0 as [hd0 tl0] using caseS'.
        intros [hd1 tl1]%uncons.
        pose (tl2 := @push c tl0 tl1).
        case hd0; simpl.
        + exact (cons hd1 tl2).
        + exact tl2.
    Defined.

    Lemma push_map [c] (s0 s1 : t c) f:
      push s0 (Vector.map f s1) = Vector.map f (push s0 s1).
    Proof.
      induction c; simpl.
      - reflexivity.
      - destruct s0 as [h ?] using caseS'; destruct s1 using caseS'; simpl.
        rewrite IHc.
        case h; reflexivity.
    Qed.

    Lemma sub_push [c] (s0 s1 : t c):
      sub (sub c s0) (push s0 s1) = sub c (and s0 s1).
    Proof.
      induction c; simpl.
      - reflexivity.
      - destruct s0 as [h0 ?] using caseS'; destruct s1 using caseS'; simpl.
        case h0; simpl; rewrite IHc; reflexivity.
    Qed.
    
    Fixpoint pull [c : CTX.t] : forall (s0 : t c), t (sub c s0) -> t (sub c (neg s0)) -> t c.
    Proof.
      case c as [|c0 c].
      - intros ? _ _; exact nil.
      - intro s0.
        case s0 as [hd0 tl0] using caseS'.
        case hd0; simpl.
        + intros [hd1 tl1]%uncons s2.
          exact (cons hd1 (pull c tl0 tl1 s2)).
        + intros s1 [hd2 tl2]%uncons.
          exact (cons hd2 (pull c tl0 s1 tl2)).
    Defined.

    Lemma map_pull c s0 s1 s2 f:
      Vector.map f (@pull c s0 s1 s2) = pull s0 (Vector.map f s1) (Vector.map f s2).
    Proof.
      induction c as [|c0 c].
      - reflexivity.
      - case s0 as [[] s0] using caseS'; cbn in *.
        + case s1 as [] using caseS'; cbn; f_equal; apply IHc.
        + case s2 as [] using caseS'; cbn; f_equal; apply IHc.
    Qed.

    Lemma sl_pull c s0 s1 s2:
      SLprop.eq (sl (sub c (pull s0 s1 s2)))
                (sl (sub (sub c s0) s1) ** sl (sub (sub c (neg s0)) s2)).
    Proof.
      induction c as [|c0 c].
      - simpl; SL.normalize; reflexivity.
      - case s0 as [[] s0] using caseS'.
        + case s1 as [[]] using caseS'; simpl;
            rewrite IHc; SL.normalize; reflexivity.
        + case s2 as [[]] using caseS'; simpl;
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
    - intros [b s]%Sub.uncons.
      exact (sl_opt (sla a) b ** sl_sub c s)%slprop.
  Defined.

  Lemma sl_sub_eq (c : CTX.t) (s : Sub.t c):
    SLprop.eq (sl (sub c s)) (sl_sub c s).
  Proof.
    induction c as [|a c]; cbn.
    - reflexivity.
    - case s as [hd s] using Sub.caseS'; cbn.
      case hd; cbn; rewrite IHc; SL.normalize; reflexivity.
  Qed.


  Lemma sl_split (c : t) (s : Sub.t c):
    SLprop.eq (sl c) (sl (sub c s) ** sl (sub c (Sub.neg s))).
  Proof.
    induction c; simpl.
    - SL.normalize; reflexivity.
    - case s as [hd tl] using Sub.caseS'; cbn.
      rewrite (IHc tl).
      case hd; cbn; SL.normalize.
      + reflexivity.
      + apply SLprop.star_comm12.
  Qed.

  Module Trf.
    Section Trf.
      Variables c0 c1 : CTX.t.
      Definition rev_f_t := Sub.t c1 -> (Sub.t c0 * CTX.t (* rem *)).

      Local Set Implicit Arguments.
      Record p (rev_f : rev_f_t) : Prop := {
        fwd : SLprop.imp (sl c0) (sl c1);
        bwd : forall s1 : Sub.t c1, let (s0, rem) := rev_f s1 in
              SLprop.imp (sl_sub c1 s1) (sl_sub c0 s0 ** sl rem)
      }.

      Definition t : Type := {rev_f : rev_f_t | p rev_f}.

      Lemma t_fwd (p : t) : SLprop.imp (sl c0) (sl c1).
      Proof.
        case p as [? [fwd _]].
        exact fwd.
      Qed.
    End Trf.
    Global Arguments Trf.p : clear implicits.

    Definition inj_p (c0 c1 add : CTX.t) (rev_f : rev_f_t c0 (c1 ++ add)) : Prop :=
      Trf.p c0 (c1 ++ add) rev_f.

    Section Refl.
      Variable c : CTX.t.
      
      Definition refl_rev_f : rev_f_t c c :=
        fun s => (s, nil).

      Lemma refl_p : Trf.p c c refl_rev_f.
      Proof.
        split; cbn; intros; SL.normalize; reflexivity.
      Qed.
    End Refl.
    Section Trans.
      Context [c0 c1 c2 : CTX.t] (f0 : rev_f_t c0 c1) (f1 : rev_f_t c1 c2).

      Definition trans_rev_f : rev_f_t c0 c2 :=
        fun s2 => let (s1, rem1) := f1 s2 in
                  let (s0, rem0) := f0 s1 in
                  (s0, rem0 ++ rem1).

      Lemma trans_p (T0 : Trf.p c0 c1 f0) (T1 : Trf.p c1 c2 f1) : Trf.p c0 c2 trans_rev_f.
      Proof.
        split.
        - rewrite (fwd T0), (fwd T1); reflexivity.
        - unfold trans_rev_f; intro s2.
          specialize (bwd T1 s2); case f1 as (s1, rem1).
          specialize (bwd T0 s1); case f0 as (s0, rem0).
          cbn; intros E0 ->.
          etransitivity. { apply SLprop.star_morph_imp. exact E0. reflexivity. }
          rewrite sl_app; SL.normalize; reflexivity.
      Qed.
    End Trans.
    Section Atom.
      Definition atomt (rev : bool) (c0 c1 : CTX.t) :=
        if rev
        then SLprop.eq  (sl c0) (sl c1)
        else SLprop.imp (sl c0) (sl c1).

      Lemma atom_imp [rev c0 c1] (T : atomt rev c0 c1) : SLprop.imp (sl c0) (sl c1).
      Proof.
        destruct rev; cbn in T; rewrite T; reflexivity.
      Qed.

      Definition atom_rev_f (rev : bool) (c0 c1 : CTX.t) : rev_f_t c0 c1 :=
        fun s1 =>
        if andb rev (Vector.allb s1)
        then (Vector.const true  (length c0), nil)
        else (Vector.const false (length c0), CTX.sub c1 s1).

      Lemma atom_p [rev c0 c1] (T : atomt rev c0 c1) : Trf.p c0 c1 (atom_rev_f rev c0 c1).
      Proof.
        split.
          { apply (atom_imp T). }
        intro s1.
        destruct rev; unfold atom_rev_f; cbn in *;
          [case (BoolSpec_of_iff (Vector.allb_iff_const s1)) as [->|_]|]; cbn.
        2,3:rewrite <-!sl_sub_eq, Sub.sub_const_false; SL.normalize; reflexivity.
        rewrite <-!sl_sub_eq, !Sub.sub_const_true, T; SL.normalize; reflexivity.
      Qed.
    End Atom.
    Section Cons. 
      Variables (a : CTX.atom) (c0 c1 : CTX.t) (f : rev_f_t c0 c1).

      Definition cons_rev_f : rev_f_t (a :: c0) (a :: c1) :=
        fun s1 =>
        let (b,   s1) := Vector.uncons (n := length c1) s1 in
        let (s0, rem) := f s1 in
        (Vector.cons _ b (length c0) s0, rem).

      Lemma cons_p (T : Trf.p c0 c1 f) : Trf.p (a :: c0) (a :: c1) cons_rev_f.
      Proof.
        split.
        - apply SLprop.star_morph_imp. reflexivity. exact (fwd T).
        - intro s1; case s1 as [b s1] using Vector.caseS'; cbn.
          specialize (bwd T s1); case (f s1) as (s0, rem); cbn; intro E.
          SL.normalize.
          eapply SLprop.star_morph_imp. reflexivity.
          exact E.
      Qed.
    End Cons.
    Section Swap.
      Context (a0 a1 : CTX.atom) [c0 c1 : CTX.t] (f : rev_f_t c0 c1).

      Definition swap_rev_f : rev_f_t (a0 :: a1 :: c0) (a1 :: a0 :: c1) :=
        fun s1 =>
        let (b1,  s1) := Vector.uncons (n := S (length c1)) s1 in
        let (b0,  s1) := Vector.uncons (n :=    length c1 ) s1 in
        let (s0, rem) := f s1 in
        (Vector.cons _ b0 (S (length c0)) (Vector.cons _ b1 (length c0) s0), rem).

      Lemma swap_p (T : Trf.p c0 c1 f) : Trf.p (a0 :: a1 :: c0) (a1 :: a0 :: c1) swap_rev_f.
      Proof.
        split.
        - cbn; rewrite SLprop.star_comm12.
          do 2 (apply SLprop.star_morph_imp; [reflexivity|]).
          exact (fwd T).
        - intro s1;
            case s1 as [b1 s1] using Vector.caseS';
            case s1 as [b0 s1] using Vector.caseS';
            cbn.
          specialize (bwd T s1); case (f s1) as (s0, rem); cbn; intro E.
          rewrite SLprop.star_comm12; SL.normalize.
          do 2 (eapply SLprop.star_morph_imp; [reflexivity|]).
          exact E.
      Qed.
    End Swap.
    Section App.
      Context [ca0 ca1 : CTX.t] (fa : rev_f_t ca0 ca1)
              [cb0 cb1 : CTX.t] (fb : rev_f_t cb0 cb1).

      Definition app_rev_f : rev_f_t (ca0 ++ cb0) (ca1 ++ cb1)
        := fun s1 =>
        let (s1a, s1b) := Sub.split ca1 cb1 s1 in
        let (s0a, rea) := fa s1a in
        let (s0b, reb) := fb s1b in
        (Sub.app s0a s0b, rea ++ reb).

      Lemma app_p (Ta : Trf.p ca0 ca1 fa) (Tb : Trf.p cb0 cb1 fb)
        : Trf.p (ca0 ++ cb0) (ca1 ++ cb1) app_rev_f.
      Proof.
        split.
        - rewrite !sl_app.
          apply SLprop.star_morph_imp.
          + apply Ta.
          + apply Tb.
        - intro s1; unfold app_rev_f.
          specialize (Sub.app_split ca1 cb1 s1).
          case Sub.split as (s1a, s1b).
          specialize (bwd Tb s1b); specialize (bwd Ta s1a).
          case fa as (s0a, rea), fb as (s0b, reb).
          cbn; intros Ea Eb ->.
          rewrite <-!sl_sub_eq, !Sub.sub_app, !sl_app, !sl_sub_eq.
          etransitivity.
          + apply SLprop.star_morph_imp. exact Ea. exact Eb.
          + SL.normalize.
            setoid_rewrite SLprop.star_comm12 at 2.
            reflexivity.
      Qed.
    End App.

    Global Arguments refl_rev_f  !c !_.
    Global Arguments trans_rev_f !c0 !c1 !c2 _ _ !_.
    Global Arguments atom_rev_f  !rev !c0 !c1 !_.
    Global Arguments cons_rev_f  _ !c0 !c1 _ !_.
    Global Arguments swap_rev_f  _ _ !c0 !c1 _ !_.
    Global Arguments app_rev_f   !ca0 !ca1 _ !cb0 !cb1 _ !_.

    Module Tac.
      (* Tactic to build a [Trf.p] or a [Trf.inj_p] *)

      Import Util.Tac.

      Definition elim_rule (rev : bool) (a : atom) (r : CTX.t) :=
        atomt rev [a] r.

      (* [PT] and [PF] must be propositions solvable using [split] (typically equalities).
         [PT] is enforced when the transformation is committed and should define the selector of
         [a] from the selectors of [r].
         [PF] is enforced when the transformation is cancelled and should define the selectors of
         [r] from the selector of [a]. *)
      Record intro_rule (rev : bool) (a : atom) (r : CTX.t) (PT PF : Prop) : Prop := mk_intro_rule {
        get_intro_rule : forall (E : PT), atomt rev r [a]
      }.
      Global Arguments get_intro_rule [_ _ _ _ _].

      Definition unfold_rule (a b : atom) := a = b.

      (* Database for automatic introduction/elimination rules.
         Called on goals:
           [elim_rule ?rev a ?r]
           [intro_rule ?rev a ?r ?PT ?PF]
           [unfold_rule a ?b]
       *)
      Global Create HintDb CtxTrfDB discriminated.
      Global Hint Constants Opaque : CtxTrfDB.
      Global Hint Variables Opaque : CtxTrfDB.

      Definition ord_t := option (list nat).

      Definition ord_le (i0 i1 : ord_t) : bool :=
        match i1, i0 with
        | None,    _       => true
        | Some _,  None    => false
        | Some l1, Some l0 =>
            (fix cmp_list l0 l1 {struct l0} :=
             match l0, l1 with
             | x0 :: l0, x1 :: l1 =>
                 match Nat.compare x0 x1 with
                 | Lt => true
                 | Gt => false
                 | Eq => cmp_list l0 l1
                 end
             | nil, nil => true
             | _,   _   => true (* placeholder *)
             end) l0 l1
        end.

      Section WitA.
        Inductive wit_A : CTX.atom -> Type :=
          | WitAAtom (i : ord_t) (a : atom) : wit_A a
          | WitATrf [rev : bool] [a : atom] [r : CTX.t] (T : Trf.atomt rev [a] r)
              (C : ForallT wit_A r) : wit_A a.

        Definition wit_Al0_res
          (R : forall (a : atom) (w : wit_A a), list (ord_t * atom))
          [r : CTX.t] (C : ForallT wit_A r) : list (ord_t * atom) :=
          concat (ForallT_join R r C).
        Fixpoint wit_A_res [a : atom] (w : wit_A a) {struct w} : list (ord_t * atom) :=
          match w with
          | WitAAtom a i => [(a, i)]
          | WitATrf _ C  => wit_Al0_res (@wit_A_res) C
          end.
        Definition wit_Al_res [r] C := @wit_Al0_res (@wit_A_res) r C.

        Definition wit_Al0_rev_f
          (R : forall (a : atom) (w : wit_A a), rev_f_t [a] (map snd (wit_A_res w)))
          : forall [r : CTX.t] (C : ForallT wit_A r),
          rev_f_t r (map snd (wit_Al_res C)).
        Proof.
          fix rc 2; intros ? [|a r w C]; cbn.
          - exact (refl_rev_f nil).
          - rewrite List.Transp.map_app.
            exact (app_rev_f (R a w) (rc r C)).
        Defined.
        Fixpoint wit_A_rev_f [a : atom] (w : wit_A a) {struct w} : rev_f_t [a] (map snd (wit_A_res w)) :=
          match w with
          | WitAAtom i a => refl_rev_f [a]
          | @WitATrf rev a r T C =>
              trans_rev_f (atom_rev_f rev [a] r) (@wit_Al0_rev_f (@wit_A_rev_f) r C)
          end.
        Definition wit_Al_rev_f [r] C := @wit_Al0_rev_f (@wit_A_rev_f) r C.

        Lemma wit_Al0_trf
          (R : forall (a : atom) (w : wit_A a), Trf.p [a] (map snd (wit_A_res w)) (wit_A_rev_f w))
          : forall [r : CTX.t] (C : ForallT wit_A r),
          Trf.p r (map snd (wit_Al_res C)) (wit_Al_rev_f C).
        Proof.
          fix IH 2.
          intros _ [|a r w C]; cbn.
          * apply refl_p.
          * unfold eq_rect_r; case eq_sym; cbn.
            exact (app_p _ _ (R a w) (IH r C)).
        Defined.
        Lemma wit_A_trf [a : atom] (w : wit_A a):
          Trf.p [a] (map snd (wit_A_res w)) (wit_A_rev_f w).
        Proof.
          revert a w; fix IH 2.
          intros _ [|rev a r T C]; cbn.
          - apply refl_p.
          - eapply trans_p.
            + apply (atom_p T).
            + exact (wit_Al0_trf IH C).
        Qed.
        Definition wit_Al_trf [r] C := @wit_Al0_trf (@wit_A_trf) r C.
      End WitA.
      Section WitB.
        Inductive wit_B : atom -> Type :=
          | WitBAtom (a : atom) : wit_B a
          | WitBTrf [rev : bool] [a : atom] [r : CTX.t] (T : Trf.atomt rev r [a])
              (C : ForallT wit_B r) : wit_B a.

        Definition wit_Bl0_res
          (R : forall (a : atom) (w : wit_B a), CTX.t)
          [r : CTX.t] (C : ForallT wit_B r) : CTX.t :=
          concat (ForallT_join R r C).
        Fixpoint wit_B_res [a : atom] (w : wit_B a) {struct w} : CTX.t :=
          match w with
          | WitBAtom a => [a]
          | WitBTrf _ C  => wit_Bl0_res (@wit_B_res) C
          end.
        Definition wit_Bl_res [r] C := @wit_Bl0_res (@wit_B_res) r C.

        Definition wit_Bl0_rev_f
          (R : forall (a : atom) (w : wit_B a), rev_f_t (wit_B_res w) [a])
          : forall [r : CTX.t] (C : ForallT wit_B r),
          rev_f_t (wit_Bl_res C) r.
        Proof.
          fix rc 2; intros ? [|a r w C]; cbn.
          - exact (refl_rev_f nil).
          - exact (app_rev_f (R a w) (rc r C)).
        Defined.
        Fixpoint wit_B_rev_f [a : atom] (w : wit_B a) {struct w} : rev_f_t (wit_B_res w) [a] :=
          match w with
          | WitBAtom a => refl_rev_f [a]
          | @WitBTrf rev a r T C =>
              trans_rev_f (@wit_Bl0_rev_f (@wit_B_rev_f) r C) (atom_rev_f rev r [a])
          end.
        Definition wit_Bl_rev_f [r] C := @wit_Bl0_rev_f (@wit_B_rev_f) r C.

        Lemma wit_Bl0_trf
          (R : forall (a : atom) (w : wit_B a), Trf.p (wit_B_res w) [a] (wit_B_rev_f w))
          : forall [r : CTX.t] (C : ForallT wit_B r),
          Trf.p (wit_Bl_res C) r (wit_Bl_rev_f C).
        Proof.
          fix IH 2.
          intros _ [|a r w C]; cbn.
          * apply refl_p.
          * exact (app_p _ _ (R a w) (IH r C)).
        Defined.
        Lemma wit_B_trf [a : atom] (w : wit_B a):
          Trf.p (wit_B_res w) [a] (wit_B_rev_f w).
        Proof.
          revert a w; fix IH 2.
          intros _ [|rev a r T C]; cbn.
          - apply refl_p.
          - eapply trans_p.
            + exact (wit_Bl0_trf IH C).
            + apply (atom_p T).
        Qed.
        Definition wit_Bl_trf [r] C := @wit_Bl0_trf (@wit_B_trf) r C.
      End WitB.
      Section Sort.
        Fixpoint trf_insert (n : ord_t) (x : atom) (l : list (ord_t * atom)) {struct l}:
          { l' : list (ord_t * atom) & rev_f_t (x :: List.map snd l) (List.map snd l') }.
        Proof.
          case l as [|(n', x') l].
          - exists [(n,x)].
            apply refl_rev_f.
          - case (ord_le n n').
            + exists ((n, x) :: (n', x') :: l).
              apply refl_rev_f.
            + case (trf_insert n x l) as [l' f].
              exists ((n', x') :: l').
              eapply trans_rev_f; cbn.
              * apply swap_rev_f, refl_rev_f.
              * apply cons_rev_f, f.
        Defined.

        Lemma trf_insert_correct n x l:
          let '(existT _ l' f) := trf_insert n x l in
          Trf.p (x :: map snd l) (map snd l') f.
        Proof.
          induction l as [|(n', x') l IH]; cbn; [|case ord_le]; cbn.
          1,2:split; apply refl_p.
          destruct trf_insert as [l' f]; cbn.
          apply trans_p.
          - apply swap_p, refl_p.
          - apply cons_p, IH.
        Qed.

        Fixpoint trf_sort_list (l : list (ord_t * atom)) {struct l} :
          { l' : list (ord_t * atom) & rev_f_t (List.map snd l) (List.map snd l') }.
        Proof.
          case l as [|(n, x) l].
          - refine (existT _ nil _).
            apply refl_rev_f.
          - case (trf_sort_list   l) as [l0 f0].
            case (trf_insert n x l0) as [l1 f1].
            exists l1.
            eapply trans_rev_f.
            + apply cons_rev_f, f0.
            + exact f1.
        Defined.

        Lemma trf_sort_list_correct l:
          let '(existT _ l' f) := trf_sort_list l in
          Trf.p (map snd l) (map snd l') f.
        Proof.
          induction l as [|(n, x) l IH]; cbn.
          - apply refl_p.
          - destruct trf_sort_list as [l0 f0].
            specialize (trf_insert_correct n x l0) as IC.
            destruct trf_insert    as [l1 f1].
            apply trans_p.
            + apply cons_p, IH.
            + apply IC.
        Qed.

        Variable l : list (ord_t * atom).

        Definition trf_sort_res : CTX.t :=
          map snd (projT1 (trf_sort_list l)).

        Definition trf_sort_rev_f : rev_f_t (map snd l) trf_sort_res :=
          projT2 (trf_sort_list l).

        Lemma trf_sort_correct:
          Trf.p (map snd l) trf_sort_res trf_sort_rev_f.
        Proof.
          unfold trf_sort_res, trf_sort_rev_f.
          specialize (trf_sort_list_correct l).
          destruct trf_sort_list as [res f]; cbn.
          auto.
        Qed.
      End Sort.
      Section Helpers.
        Definition rord_t := list nat.
        Definition ord_of_r (r : rord_t) : ord_t := Some (rev_append r []).
        Definition ord_None : ord_t := None.

        Inductive state_A (a : atom) :=
          | StAFirst (wit : wit_A a)
          | StATrf   (n : ord_t) (committed : option bool).
        Global Arguments StAFirst [_].
        Global Arguments StATrf   [_].
        Inductive A (a : atom) (s : state_A a) (p : list bool) := mk_A.

        Record committed_B_t := mk_cb {
          cb_PT : Prop;
          cb_PF : Prop;
          cb_c  : {cb_PT}+{cb_PF};
        }.
        Inductive state_B (a : atom) :=
          | StBFirst (wit : wit_B a)
          | StBTrf   (committed : option committed_B_t).
        Global Arguments StBFirst [_].
        Global Arguments StBTrf   [_].
        Inductive B (a : atom) (n : rord_t) (s : state_B a) (p : list committed_B_t) := mk_B.

        Record trf_wit (c0 c1 : CTX.t) := mk_trf_wit {
          w_witA : ForallT wit_A c0;
          w_witB : ForallT wit_B c1;
        }.
        Global Arguments mk_trf_wit [_ _].

        Definition intro_wit_A (ps : list bool) : Type -> CTX.t -> Type :=
          List.fold_right (fun a T => {w : wit_A a & A a (StAFirst w) ps -> T}).
        Fixpoint intro_wit_B (ps : list committed_B_t) (n : nat) (ntl : rord_t)
          (T : Type) (c1 : CTX.t) {struct c1} : Type :=
          match c1 with
          | nil     => T
          | a :: c1 =>
              let T := intro_wit_B ps (S n) ntl T c1 in
              {w : wit_B a & B a (n :: ntl) (StBFirst w) ps -> T}
          end.
        Definition intro_wit_trf (c0 c1 : CTX.t) : Type :=
          intro_wit_B nil O nil (intro_wit_A nil True c0) c1.

        Fixpoint wit_of_intro_A [ps T c0] {struct c0}:
          forall (W : intro_wit_A ps T c0), ForallT wit_A c0 * T.
        Proof.
          case c0 as [|a c0]; cbn.
          - intro W. split. constructor. exact W.
          - intros [w W].
            ecase wit_of_intro_A as [y x]. { apply W. split. }
            split. constructor.
            exact w. exact y. exact x.
        Defined.

        Fixpoint wit_of_intro_B [ps n ntl T c1] {struct c1}:
          forall (W : intro_wit_B ps n ntl T c1), ForallT wit_B c1 * T.
        Proof.
          case c1 as [|a c1]; cbn.
          - intro W. split. constructor. exact W.
          - intros [w W].
            ecase wit_of_intro_B as [y x]. { apply W. split. }
            split. constructor.
            exact w. exact y. exact x.
        Defined.

        Definition wit_of_intro_trf [c0 c1] (W : intro_wit_trf c0 c1) : trf_wit c0 c1 :=
          let (wB, W) := wit_of_intro_B W in
          let (wA, _) := wit_of_intro_A W in
          mk_trf_wit wA wB.
      End Helpers.

      Global Arguments wit_Al_rev_f   !r !C !_.
      Global Arguments wit_A_rev_f    _ !w !_.
      Global Arguments wit_Bl_rev_f   !r !C !_.
      Global Arguments wit_B_rev_f    _ !w !_.
      Global Arguments trf_insert     _ _ !l.
      Global Arguments trf_sort_list  !l.
      Global Arguments trf_sort_rev_f !l _.

      Local Lemma build_trf_lem (c0 c1 : CTX.t)
        (W : intro_wit_trf c0 c1)
        (wA : ForallT wit_A c0) (wB : ForallT wit_B c1)
        (EW : mk_trf_wit wA wB = wit_of_intro_trf W):
        let c0_0 := wit_Al_res wA     in
        let c0_1 := trf_sort_res c0_0 in
        let c1_0 := wit_Bl_res wB     in
        forall (E : c1_0 = c0_1),
        Trf.p c0 c1
          (@trans_rev_f c0 c0_1 c1 (@trans_rev_f c0 (map snd c0_0) c0_1
            (wit_Al_rev_f wA)
            (trf_sort_rev_f c0_0))
            (eq_rect c1_0 (fun c => rev_f_t c c1) (wit_Bl_rev_f wB) c0_1 E)).
      Proof.
        clear W EW.
        intros c0_0 c0_1 c1_0 E.
        set (f0 := trans_rev_f _ _) at 2.
        assert (Trf.p c0 c0_1 f0) as T0. {
          apply trans_p.
          - apply wit_Al_trf.
          - apply trf_sort_correct.
        }
        clearbody f0 c0_1; clear c0_0; destruct E; cbn.
        apply trans_p.
        - exact T0.
        - apply wit_Bl_trf.
      Qed.

      Local Lemma build_inj_lem (c0 c1 add : CTX.t)
        (W : intro_wit_trf c0 c1)
        (wA : ForallT wit_A c0) (wB : ForallT wit_B c1)
        (EW : mk_trf_wit wA wB = wit_of_intro_trf W):
        let c0_0 := wit_Al_res wA     in
        let c0_1 := trf_sort_res c0_0 in
        let c1_0 := wit_Bl_res wB     in
        forall (E : c1_0 ++ add = c0_1),
        Trf.inj_p c0 c1 add
          (@trans_rev_f c0 c0_1 (c1 ++ add) (@trans_rev_f c0 (map snd c0_0) c0_1
            (wit_Al_rev_f wA)
            (trf_sort_rev_f c0_0))
            (eq_rect (c1_0 ++ add) (fun c => rev_f_t c (c1 ++ add))
              (app_rev_f (wit_Bl_rev_f wB) (refl_rev_f add)) c0_1 E)).
      Proof.
        clear W EW.
        intros c0_0 c0_1 c1_0 E.
        set (f0 := trans_rev_f _ _) at 2.
        assert (Trf.p c0 c0_1 f0) as T0. {
          apply trans_p.
          - apply wit_Al_trf.
          - apply trf_sort_correct.
        }
        clearbody f0 c0_1; clear c0_0; destruct E; cbn.
        apply trans_p.
        - exact T0.
        - apply app_p.
          + apply wit_Bl_trf.
          + apply refl_p.
      Qed.

      Ltac intro_wit_goal :=
        cbn;
        repeat (simple refine (existT _ _ _); [shelve|intro]).

      Ltac commit_trf_A b :=
        unify b true.

      Ltac commit_parents_A ps :=
        lazymatch ps with
        | ?b :: ?ps =>
            tryif is_evar b
            then (commit_trf_A b; commit_parents_A ps)
            else idtac
        | nil => idtac
        end.

      Ltac commit_trf_B c :=
        build_term c ltac:(fun _ => left; solve [split]).
 
      Ltac commit_parents_B ps :=
        lazymatch ps with
        | mk_cb _ _ ?c :: ?ps =>
            tryif is_evar c
            then (commit_trf_B c; commit_parents_B ps)
            else idtac
        | nil => idtac
        end.

      Ltac cancel_tr_opt_A c :=
        lazymatch c with
        | None    => idtac
        | Some ?c => unify c false
        end.

      Ltac cancel_tr_opt_B c :=
        lazymatch c with
        | None                => idtac
        | Some (mk_cb _ _ ?c) => Util.Tac.build_term c ltac:(fun _ => right; solve [split])
        end.

      Ltac mark_A n sA :=
        lazymatch sA with
        | @StAFirst ?a  ?w => unify w (WitAAtom n a)
        | StATrf    ?n' ?c => unify n' n; cancel_tr_opt_A c
        end.

      Ltac mark_B sB :=
        lazymatch sB with
        | @StBFirst ?a ?w => unify w (WitBAtom a)
        | StBTrf    ?c    => cancel_tr_opt_B c
        end.

      Ltac clear_A sA :=
        lazymatch sA with
        | @StAFirst ?a ?w  =>
            unify w (WitAAtom ord_None a)
        | StATrf ?n ?c =>
            unify n ord_None;
            cancel_tr_opt_A c
        end.

      Ltac clear_B sB :=
        lazymatch sB with
        | @StBFirst ?a ?w  =>
            unify w (WitBAtom a)
        | StBTrf ?c =>
            cancel_tr_opt_B c
        end.

      Ltac clean_hyps :=
        repeat lazymatch goal with
        | H : A _ (StATrf ?n (Some true)) _ |- _ =>
            unify n ord_None;
            clear H
        | H : B _ _ (StBTrf (Some (mk_cb _ _ (left _)))) _ |- _ =>
            clear H
        | H : A _   ?sA (false :: _) |- _ =>
            clear_A sA;
            clear H
        | H : B _ _ ?sB (mk_cb _ _ (right _) :: _) |- _ =>
            clear_B sB;
            clear H
        end.


      Ltac match_hyps :=
        lazymatch reverse goal with
        | HB : B (existT _ ?v ?slB) ?n ?sB ?pB, HA : A (existT _ ?v ?slA) ?sA ?pA |- _ =>
            (* idtac "MATCH" v; *)
            unify slB slA;
            mark_A (ord_of_r n) sA;
            mark_B sB;
            commit_parents_A pA;
            commit_parents_B pB;
            clear HA HB;
            clean_hyps;
            match_hyps
        | _ => idtac
        end.

      (* reverts the hypotheses [StAFirst] and [StBFirst] *)
      Lemma forall_to_arrow [A : Type] [B0 : A -> Type] [B1 : Type]
        (E : forall x : A, B0 x = B1)
        (C : A -> B1):
        forall x : A, B0 x.
      Proof.
        intro x; rewrite E; apply (C x).
      Qed.

      Ltac revert_hyps_first fl :=
        lazymatch goal with
        | H : A _   (StAFirst _) _ |- _ => idtac
        | H : B _ _ (StBFirst _) _ |- _ => idtac
        | _ => fl tt
        end;
        repeat (
          lazymatch goal with
          | H : A _   (StAFirst _) _ |- _ => revert H
          | H : B _ _ (StBFirst _) _ |- _ => revert H
          end;
          simple refine (forall_to_arrow _ _); [shelve|reflexivity|]
        ).

      (* try to apply transformations (auto intro/elim) *)
      Lemma rewrite_elim_rule [rev a a' r]
        (E : unfold_rule a a')
        (C : elim_rule rev a' r):
        elim_rule rev a r.
      Proof.
        rewrite E. exact C.
      Qed.

      Lemma apply_trf_A (a : atom) (w : wit_A a) (ps : list bool)
        [rev : bool] [r : CTX.t]
        (T : elim_rule rev a r)
        [n : ord_t] [committed : bool] (G : Type)
        (C : A a (StATrf n (Some committed)) ps -> intro_wit_A (committed :: ps) G r)
        (W : w = if committed
                 then @WitATrf rev a r T (fst (wit_of_intro_A (C (mk_A _ _ _))))
                 else @WitAAtom n a)
        (H : A a (StAFirst w) ps): G.
      Proof.
        apply (wit_of_intro_A (C (mk_A _ _ _))).
      Qed.

      Lemma no_trf_A (a : atom) (w : wit_A a) (ps : list bool)
        (G : Type)
        [n : ord_t]
        (C : A a (StATrf n None) ps -> G)
        (W : w = WitAAtom n a)
        (H : A a (StAFirst w) ps) : G.
      Proof.
        apply C; constructor.
      Qed.

      Lemma rewrite_intro_rule [rev a a' r PT PF]
        (E : unfold_rule a a')
        (C : intro_rule rev a' r PT PF):
        intro_rule rev a r PT PF.
      Proof.
        rewrite E. exact C.
      Qed.

      Lemma apply_trf_B (a : atom) (n : rord_t) (w : wit_B a) (ps : list committed_B_t)
        [rev : bool] [r : CTX.t] [PT PF : Prop]
        (T : intro_rule rev a r PT PF)
        [committed : {PT}+{PF}] (G : Type)
        (C : B a n (StBTrf (Some (mk_cb PT PF committed))) ps ->
             intro_wit_B (mk_cb PT PF committed :: ps) O n G r)
        (W : w = match committed with
                 | left pf => @WitBTrf rev a r (get_intro_rule T pf)
                                               (fst (wit_of_intro_B (C (mk_B _ _ _ _))))
                 | right _ => @WitBAtom a
                 end)
        (H : B a n (StBFirst w) ps): G.
      Proof.
        apply (wit_of_intro_B (C (mk_B _ _ _ _))).
      Qed.

      Lemma no_trf_B (a : atom) (n : rord_t) (ps : list committed_B_t)
        (G : Type)
        (C : B a n (StBTrf None) ps -> G)
        (H : B a n (StBFirst (WitBAtom a)) ps): G.
      Proof.
        apply C; constructor.
      Qed.

      Ltac apply_trf slv rfl k :=
        lazymatch goal with
        | |- A ?a (StAFirst ?w) ?ps -> ?G =>
            let Tr := fresh "Tr" in
            tryif
              unshelve epose proof (Tr := apply_trf_A a w ps _);
              [ (* rev *) shelve | (* r *) shelve
              | (* T *)
                repeat (refine (rewrite_elim_rule _ _); [slv tt |]);
                slv tt | ]
            then (
              simple refine (Tr _ _ G _ _); clear Tr;
              [ (* n *) shelve | (* committed *) shelve
              | (* C *) intro; intro_wit_goal; apply_trf slv rfl k
              | (* W *) rfl tt ]
            ) else (
              simple refine (no_trf_A a w ps G _ _);
              [ (* n *) shelve
              | (* C *) intro; apply_trf slv rfl k
              | (* W *) rfl tt ]
            )
        | |- B ?a ?n (StBFirst ?w) ?ps -> ?G =>
            let Tr := fresh "Tr" in
            tryif
              unshelve epose proof (Tr := apply_trf_B a n w ps _);
              [ (* rev *) shelve | (* r *) shelve | (* PT *) shelve | (* PF *) shelve
              | (* T *)
                repeat (refine (rewrite_intro_rule _ _); [slv tt | cbn]);
                slv tt | ]
            then (
              simple refine (Tr _ G _ _); clear Tr;
              [ (* committed *) shelve
              | (* C *) intro; intro_wit_goal; apply_trf slv rfl k
              | (* W *) rfl tt ]
            ) else (
              simple refine (no_trf_B a n ps G _);
              intro; apply_trf slv rfl k
            )
        | |- True => k tt
        end.

      Ltac transform_hyps fl k :=
        revert_hyps_first fl;
        apply_trf ltac:(fun _ => solve [eauto 1 with CtxTrfDB nocore])
                  ltac:(fun _ => reflexivity)
                  k.

      Ltac build_iter fuel try_end :=
        match_hyps;
        try_end ltac:(fun fl =>
        lazymatch fuel with
        | O    => idtac "Fuel limit reached"; fl tt
        | S ?n => transform_hyps fl ltac:(fun _ =>
                  build_iter n try_end)
        end).

      Local Ltac build_until try_end :=
        intro_wit_goal;
        build_iter 10 try_end.

      (* solves a goal:
           Trf.p [mka vp0' sel0'; ... ; mka vp9' sel9']
                 [mka vp0 ?sel0 ; ... ; mka vp9 ?sel5 ]
                 ?rev_f
       *)
      Ltac build_p_end k :=
        lazymatch goal with
        | H : B ?a _ (StBFirst _) _  |- _ =>
            k ltac:(fun _ => ffail "Trf.build: remaining B" a)
        | H : B ?a _ (StBTrf None) _ |- _ =>
            k ltac:(fun _ => ffail "Trf.build: remaining B" a)
        | H : A ?a (StAFirst _) _    |- _ =>
            k ltac:(fun _ => ffail "Trf.build: remaining A" a)
        | H : A ?a (StATrf _ None) _ |- _ =>
            k ltac:(fun _ => ffail "Trf.build: remaining A" a)
        | _ =>
            iter ltac:(fun k =>
            (* commit transformations that produce no children *)
            lazymatch goal with
            | H : B _ _ (StBTrf (Some (mk_cb _ _ ?c))) _ |- _ =>
                commit_trf_B c;
                clear H; k tt
            | H : A _ (StATrf ?n (Some ?b)) _ |- _ =>
                unify n ord_None;
                commit_trf_A b;
                clear H; k tt
            | |- _ => idtac
            end);
            exact Logic.I
        end.

      Ltac build_p :=
        simple refine (build_trf_lem _ _ _ _ _ _ _);
        [ (* W *) build_until build_p_end
        | shelve | shelve | (* EW *) Tac.cbn_refl 
        | (* E *) Tac.cbn_refl ].

      (* solves a goal:
           Trf.t [mka vp0' sel0'; ... ; mka vp9' sel9']
                 [mka vp0 ?sel0 ; ... ; mka vp9 ?sel5 ]
       *)
      Ltac build_t :=
        eexists; build_p.

      (* solves a goal:
           itrf [mka vp0' sel0'; ... ; mka vp9' sel9']
                [mka vp0 ?sel0 ; ... ; mka vp9 ?sel5 ]
                ?add ?rev_f
       *)
      Ltac build_inj_p_end k :=
        lazymatch goal with
        | H : B ?a _ (StBFirst _) _ |- _ =>
            k ltac:(fun _ => ffail "Trf.build_inj: remaining B" a)
        | H : B ?a _ (StBTrf None) _ |- _ =>
            k ltac:(fun _ => ffail "Trf.build_inj: remaining B" a)
        | _ =>
            iter ltac:(fun k =>
            lazymatch goal with
            | H : B _ _ (StBTrf (Some (mk_cb _ _ ?c))) _ |- _ =>
                (* commit transformations that produce no children *)
                commit_trf_B c;
                clear H; k tt
            | H : A _ ?sA _   |- _ =>
                clear_A sA; clear H; k tt
            | |- _ => idtac
            end);
            exact Logic.I
        end.

      Ltac build_inj_p :=
        simple refine (build_inj_lem _ _ _ _ _ _ _ _);
        [ (* W *) build_until build_inj_p_end
        | shelve | shelve | (* EW *) Tac.cbn_refl
        | (* E *) Tac.cbn_refl ].


      Section Test.
        Variable v : nat -> Vprop.p nat.

        Goal exists sl0 sl1 rev_f,
          Trf.p [mka (v 0, 0); mka (v 1, 1)] [mka (v 0, sl0); mka (v 1, sl1)] rev_f.
        Proof.
          do 3 eexists.
          build_p.
        Qed.

        Goal exists sl0 sl1,
          inhabited (Trf.t [mka (v 0, 0); mka (v 1, 1)] [mka (v 0, sl0); mka (v 1, sl1)]).
        Proof.
          do 3 eexists.
          build_t.
        Qed.

        Goal exists sl0 sl1 add rev_f,
          Trf.inj_p [mka (v 1, 1); mka (v 2, 2); mka (v 0, 0)] [mka (v 0, sl0); mka (v 1, sl1)] 
            add rev_f.
        Proof.
          do 4 eexists.
          build_inj_p.
        Qed.


        Variable w : Vprop.p (nat * nat).

        Hypothesis W_elim  : forall sel, atomt false [mka (w, sel)] [mka (v 0, fst sel); mka (v 1, snd sel)].
        Hypothesis W_intro : forall sl0 sl1, atomt true [mka (v 0, sl0); mka (v 1, sl1)] [mka (w, (sl0, sl1))] .

        Definition W_lem_elim : forall sel,
          elim_rule _ (existT _ {| Vprop.sl := w |} sel) _ := W_elim.
        Lemma W_lem_intro sel sl0 sl1:
          intro_rule true (existT _ {| Vprop.sl := w |} sel) [mka (v 0, sl0); mka (v 1, sl1)]
            (sel = (sl0, sl1)) ((sl0, sl1) = (fst sel, snd sel)).
        Proof.
          constructor; intros ->.
          apply W_intro.
        Qed.

        Local Hint Resolve W_lem_elim  | 1 : CtxTrfDB.
        Local Hint Extern 1 (intro_rule _ (existT _ {| Vprop.sl := w |} _) _ _ _) =>
          eapply W_lem_intro : CtxTrfDB.

        Goal forall sl01, exists sl0 sl1 sl2 rev_f,
          Trf.p [mka (w, sl01); mka (v 2, 2)] [mka (v 0, sl0); mka (v 1, sl1); mka (v 2, sl2)] rev_f.
        Proof.
          do 4 eexists.
          build_p.
        Qed.
        
        Goal forall sl01, exists sl0 sl1 add rev_f,
          Trf.inj_p [mka (w, sl01); mka (v 2, 2)] [mka (v 0, sl0); mka (v 1, sl1)] add rev_f.
        Proof.
          do 4 eexists.
          build_inj_p.
        Qed.

        Goal exists sl,
          inhabited (Trf.t [mka (v 0, 0); mka (v 1, 1)] [mka (w, sl)]).
        Proof.
          do 2 eexists.
          build_t.
        Qed.

        Variable w' : Vprop.p (nat * nat).
        Hypothesis W'_eq : forall sel, SLprop.eq (sl [mka (w', sel)]) (sl [mka (w, sel)]).
        Definition W'_lem_elim : forall sel,
          elim_rule true (existT _ {| Vprop.sl := w' |} sel) _ := W'_eq.
        Local Hint Resolve W'_lem_elim | 1 : CtxTrfDB.

        Goal forall sl0, exists sl1 rev_f,
          Trf.p [mka (w', sl0)] [mka (w, sl1)] rev_f /\
          Tac.display (rev_f (Vector.cons _ true _ (Vector.nil _))).
        Proof.
          do 3 eexists.
          build_p.
          cbn.
          reflexivity.
        Qed.

        Variable vemp : Vprop.p unit.
        Hypothesis vemp_eq : forall sel, SLprop.eq (vemp sel) SLprop.emp.

        Lemma vemp_lem_elim : forall sel,
          elim_rule true (existT _ {| Vprop.sl := vemp |} sel) [].
        Proof.
          cbn; intro.
          rewrite vemp_eq.
          SL.normalize; reflexivity.
        Qed.
        Lemma vemp_lem_intro sel:
          intro_rule true (existT _ {| Vprop.sl := vemp |} sel) []
            (sel = tt) True.
        Proof.
          constructor; intros ->; cbn.
          rewrite vemp_eq.
          SL.normalize; reflexivity.
        Qed.

        Local Hint Resolve vemp_lem_elim | 1 : CtxTrfDB.
        Local Hint Extern 1 (intro_rule _ (existT _ {| Vprop.sl := vemp |} _) _ _ _) =>
          eapply vemp_lem_intro : CtxTrfDB.

        Goal exists sl add rev_f,
          Trf.inj_p [] [mka (vemp, sl)] add rev_f.
        Proof.
          do 3 eexists.
          Tac.build_inj_p.
        Qed.

        Goal forall sl, exists rev_f,
          Trf.p [mka (vemp, sl)] [] rev_f.
        Proof.
          eexists.
          Tac.build_p.
        Qed.
      End Test.
    End Tac.
  End Trf.
End CTX.

Module VpropList.
  Definition t := list Vprop.t.

  Definition sel  : t -> list Type := map Vprop.ty.
  Definition sel' : t -> list Type := map Vprop.sel.
  Definition sel_t (vs : t) := Tuple.t (sel vs).

  Fixpoint inst (vs : t) {struct vs} : sel_t vs -> CTX.t :=
    match vs with
    | nil     => fun _ => nil
    | v :: vs => fun '(sel, sels) => existT _ v sel :: inst vs sels
    end.

  Lemma inst_length vs sl:
    length (VpropList.inst vs sl) = length vs.
  Proof.
    induction vs; cbn.
    - reflexivity.
    - case sl as (?, sl); cbn; f_equal; auto.
  Defined.

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

  Fixpoint split_sel (v0 v1 : VpropList.t) {struct v0}:
    sel_t (v0 ++ v1) -> sel_t v0 * sel_t v1
    :=
    match v0 with
    | nil     => fun sl => (tt, sl)
    | v :: v0 => fun '(s0, sl) =>
                 let (sl0, sl1) := split_sel v0 v1 sl in
                 ((s0, sl0), sl1)
    end.

  Lemma app_split_sel (v0 v1 : VpropList.t) (sl : sel_t (v0 ++ v1)):
    let sl01 := split_sel v0 v1 sl in
    sl = app_sel (fst sl01) (snd sl01).
  Proof.
    induction v0 as [|v v0]; cbn.
    - reflexivity.
    - case sl as (s0, sl).
      rewrite (IHv0 sl) at 1.
      case split_sel; reflexivity.
  Qed.

  Lemma sub_of_ctx_eq (c : CTX.t) (sl : sel_t (of_ctx c)):
    CTX.Sub.t (inst (of_ctx c) sl) = CTX.Sub.t c.
  Proof.
    unfold CTX.Sub.t, of_ctx.
    rewrite inst_length, List.Transp.map_length.
    reflexivity.
  Defined.

  Fixpoint tr_sub_of_ctx [c : CTX.t] {struct c} :
    forall [sl : sel_t (of_ctx c)]
           (sb : CTX.Sub.t (inst (of_ctx c) sl)),
           CTX.Sub.t c.
  Proof.
    case c as [|a c]; cbn.
    - exact (fun _ _ => CTX.Sub.nil).
    - intros (sl0, sl) [b sb]%CTX.Sub.uncons.
      exact (CTX.Sub.cons b (tr_sub_of_ctx c sl sb)).
  Defined.

  Fixpoint change_ctx_sub (c : CTX.t) {struct c}:
    forall (s : CTX.Sub.t c) (sl : sel_t (of_ctx (CTX.sub c s))),
    sel_t (of_ctx c).
  Proof.
    case c as [|[v sl0] c].
    - exact (fun _ _ => tt).
    - cbn; intro s.
      case s as [[|] s] using CTX.Sub.caseS'; cbn.
      + intros (sl0', sl).
        exact (sl0', change_ctx_sub c s sl).
      + intro sl.
        exact (sl0, change_ctx_sub c s sl).
  Defined.

  Lemma change_ctx_sub_sl c s sl:
    SLprop.eq (CTX.sl (inst (of_ctx c) (change_ctx_sub c s sl)))
              (CTX.sl (CTX.sub c (CTX.Sub.neg s)) **
               CTX.sl (inst (of_ctx (CTX.sub c s)) sl)).
  Proof.
    induction c as [|[v sl0] c IH]; cbn.
    - SL.normalize; reflexivity.
    - case s as [[|] s] using CTX.Sub.caseS'; cbn.
      + case sl as (sl0', sl); cbn.
        rewrite IH, SLprop.star_comm12; reflexivity.
      + rewrite IH; SL.normalize; reflexivity.
  Qed.
End VpropList.

Module Notations.
  Notation "x ~> v" := (existT Vprop.ty (Vprop.mk x) v) (at level 100).
  Notation "x ~>"   := (Vprop.mk x) (at level 100).
  Definition vptr := SLprop.cell.
  Global Arguments vptr/.
End Notations.
Import Notations.


Module VRecord.
  Inductive p (A : Type) (vs : VpropList.t)
    (f : A -> Tuple.u_t (VpropList.sel vs))
    (g : Tuple.arrow (VpropList.sel vs) (fun _ => A))
    : Prop
  := mk_p (GF : Tuple.arrow (VpropList.sel vs) (fun sl1 => Tuple.of_u_t (f (Tuple.to_fun g sl1)) = sl1)).

  Definition v [A vs f g] (P : p A vs f g) : Vprop.p A :=
    fun x => CTX.sl (VpropList.inst vs (Tuple.of_u_t (f x))).

  Lemma elim_rule [A vs f g] (P : p A vs f g) sl:
    CTX.Trf.Tac.elim_rule true
      (VRecord.v P ~> sl) (VpropList.inst vs (Tuple.of_u_t (f sl))).
  Proof.
    unfold VRecord.v; cbn; SL.normalize.
    reflexivity.
  Qed.

  Lemma intro_rule [A vs f g] (P : p A vs f g) sl0 sl1 :
    CTX.Trf.Tac.intro_rule true
      (VRecord.v P ~> sl0) (VpropList.inst vs sl1)
      (sl0 = Tuple.to_fun g sl1) (sl1 = Tuple.of_u_t (f sl0)).
  Proof.
    constructor; intros ->; unfold v; cbn; SL.normalize.
    ecase P as [->%Tuple.to_fun].
    reflexivity.
  Qed.

  Ltac intro_rule_tac A vs f g P sl0 :=
    simple refine (@intro_rule A vs f g P sl0 _);
    Tuple.build_shape (* sl1 *).

  Module Tactics.
    #[export] Hint Resolve VRecord.elim_rule | 1 : CtxTrfDB.
    #[export] Hint Extern 1 (CTX.Trf.Tac.intro_rule _ (@VRecord.v ?A ?vs ?f ?g ?P ~> ?sl0) _ _ _) =>
      VRecord.intro_rule_tac A vs f g P sl0 : CtxTrfDB.
  End Tactics.
End VRecord.
