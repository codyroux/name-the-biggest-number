Require Import Arith.


Inductive type :=
| Nat : type
| Arrow : type -> type -> type.



(* No explicit type abstractions or applications: we don't really care about type-checking. *)
Inductive term :=
| Var : nat -> term
| App : term -> term -> term
| Abs : term -> term
| TConst : nat -> term
| TS : term -> term
| Rec : type -> term -> term -> term -> term.

(* An evaluation context is either empty, or a pair of a term and an
eval context, with the remainder of the bindings. *)
Inductive eval_ctx :=
| Empty_ctx : eval_ctx
| Push_ctx : value -> eval_ctx -> eval_ctx
with value :=
| VAbs : term -> eval_ctx -> value
| VConst : nat -> value
.

Inductive nth : eval_ctx -> nat -> value -> Prop :=
| nth_0 : forall v c, nth (Push_ctx v c) 0 v
| nth_S : forall v v' n c, nth c n v' -> nth (Push_ctx v c) (S n) v'.

Notation "[::]" := Empty_ctx.
Notation "v ::: e" := (Push_ctx v e)(at level 30, right associativity).

Check Nat.recursion.

Inductive TmEval : eval_ctx -> term -> value -> Prop :=
| Eval_var : forall ectx n v,
    nth ectx n v ->
    TmEval ectx (Var n) v
(* Weak reduction *)
| Eval_abs : forall ectx t, TmEval ectx (Abs t) (VAbs t ectx)
(* Call by value *)
| Eval_app : forall ectx ectx' t t' u v v',
    TmEval ectx t (VAbs t' ectx') ->
    TmEval ectx u v ->
    TmEval (v ::: ectx') t' v' ->
    TmEval ectx (App t u) v'
| Eval_0 : forall ectx n, TmEval ectx (TConst n) (VConst n)
| Eval_S : forall ectx t v,
    TmEval ectx t (VConst v) -> TmEval ectx (TS t) (VConst (S v))
| Eval_rec0 : forall ectx ty z s v t,
    TmEval ectx z v ->
    TmEval ectx t (VConst 0) ->
    TmEval ectx (Rec ty z s t) v
| Eval_recS : forall ectx ty z s v v' t n,
    TmEval ectx t (VConst (S n)) ->
    TmEval ectx (Rec ty z s (TConst n)) v' ->
    TmEval (v' ::: VConst n ::: ectx) s v ->
    TmEval ectx (Rec ty z s t) v
.

Inductive ty_ctx :=
| Empty_ty_ctx : ty_ctx
| Cons_ty_ctx : type -> ty_ctx -> ty_ctx.

Notation "ty :: tys" := (Cons_ty_ctx ty tys)(at level 60, right associativity).

Inductive nth_ty : ty_ctx -> nat -> type -> Prop :=
| nth_0_ty : forall ty ctx, nth_ty (Cons_ty_ctx ty ctx) 0 ty
| nth_S_ty : forall ty ty' n ctx, nth_ty ctx n ty' -> nth_ty (Cons_ty_ctx ty ctx) (S n) ty'.

Inductive has_type : forall (Γ : ty_ctx)(t : term)(ty : type), Prop :=
| has_type_var : forall Γ n ty, nth_ty Γ n ty -> has_type Γ (Var n) ty
| has_type_abs : forall Γ ty1 ty2 t,
    has_type (Cons_ty_ctx ty1 Γ) t ty2 -> has_type Γ (Abs t) (Arrow ty1 ty2)
| has_type_app : forall Γ ty1 ty2 t u,
    has_type Γ t (Arrow ty1 ty2) -> has_type Γ u ty1 -> has_type Γ (App t u) ty2
| has_type_0 : forall Γ n, has_type Γ (TConst n) Nat
| has_type_S : forall Γ t,
    has_type Γ t Nat ->
    has_type Γ (TS t) Nat
| has_type_Rec : forall Γ A z s t,
    has_type Γ z A ->
    has_type (A :: Nat :: Γ) s A ->
    has_type Γ t Nat ->
    has_type Γ (Rec A z s t) A
.

(* Sadly, this does not work... *)
Fail 
Inductive Computable_tm : type -> eval_ctx -> term -> Prop :=
| Computable_tm_eval : forall ty t ectx v,
    TmEval ectx t v ->
    Computable_val ty v -> Computable_tm ty ectx t
with Computable_val : type -> value -> Prop :=
| Comp_VConst : forall n, Computable_val Nat (VConst n)
| Comp_VAbs : forall ty1 ty2 t env, (forall v, Computable_val ty1 v -> Computable_tm ty2 (v ::: env) t) -> Computable_val (Arrow ty1 ty2) (VAbs t env)
.

Print value.

Definition Comp_Nat : value -> Prop := fun v => exists n, v = VConst n.

(* We probably need this if we don't want to define the predicates by
  recursion over type...  *)
(* Definition Computable_val_F *)
(*            (Cv : type -> value -> Prop) *)
(*            (Ct : type -> eval_ctx -> term -> Prop) := *)
(*   fun ty v => *)
(*     match ty with *)
(*     | Nat => Comp_Nat v *)
(*     | Arrow t1 t2 => *)
(*         match v with *)
(*         |VAbs t ectx => *)
(*            forall v', Cv t1 v' -> *)
(*                       Ct t2 (v' ::: ectx) t *)
(*         | _ => False *)
(*         end *)
(*     end. *)

(* Definition Computable_tm_F *)
(*            (Cv : type -> value -> Prop) *)
(*            (Ct : type -> eval_ctx -> term -> Prop) := *)
(*         fun ty ectx t => *)
(*           match ty with *)
(*           | Nat => exists v, TmEval ectx t v /\ Comp_Nat v *)
(*           | Arrow t1 t2 => *)
(*               exists t' ectx', TmEval ectx t (VAbs t' ectx') /\ *)
(*                                  forall v, *)
(*                                    Cv t1 v -> *)
(*                                    Ct t2 (v ::: ectx') t' *)
(*           end *)
(* . *)


Fixpoint Computable_val (ty : type) : value -> Prop :=
  fun v =>
    match ty with
    | Nat => Comp_Nat v
    | Arrow t1 t2 =>
        match v with
        |VAbs t ectx =>
           forall v', Computable_val t1 v' ->
                      Computable_tm t2 (v' ::: ectx) t
        | _ => False
        end
    end
      with
      Computable_tm (ty : type) : eval_ctx -> term -> Prop :=
        fun ectx t =>
          match ty with
          | Nat => exists v, TmEval ectx t v /\ Comp_Nat v
          | Arrow t1 t2 =>
              exists t' ectx', TmEval ectx t (VAbs t' ectx') /\
                                 forall v,
                                   Computable_val t1 v ->
                                   Computable_tm t2 (v ::: ectx') t'
          end
.

Inductive Computable_ctx : ty_ctx -> eval_ctx -> Prop :=
| Computable_ctx_Nil : Computable_ctx Empty_ty_ctx Empty_ctx
| Computable_ctx_Cons : forall ty v Γ ectx,
    Computable_val ty v ->
    Computable_ctx Γ ectx ->
    Computable_ctx (ty :: Γ) (v ::: ectx)
 .

Check nth_ty.
    
Lemma comp_eval : forall ty ectx t v,
    TmEval ectx t v -> Computable_val ty v -> Computable_tm ty ectx t.
Proof.
  induction ty; simpl.
  - intros; eexists; eauto.
  - intros ectx t v; destruct v; intros; try contradiction.
    exists t0, e; split; auto.
Qed.

Lemma nth_det : forall ectx n v v', nth ectx n v -> nth ectx n v' -> v = v'.
Proof.
  intros ectx n v v' h; induction h; intros h'; inversion h'; auto.
Qed.

(* FIXME: cleanup *)
Lemma eval_det : forall ectx t v v',
    TmEval ectx t v -> TmEval ectx t v' -> v = v'.
Proof.
  intros ectx t v v' h; revert v'; induction h; intros ? h'.
  - inversion h'; subst; try congruence.
    eapply nth_det; eauto.
  - inversion h'; subst; try congruence.
  - inversion h'; try congruence; subst.
    assert (h4 := IHh1 (VAbs t'0 ectx'0) H1).
    inversion h4; subst; clear h4.
    assert (h4 := IHh2 v0 H3); subst; auto.
  - inversion h'; subst; try congruence.
  - inversion h'; subst; try congruence.
    repeat f_equal.
    assert (h'' := IHh (VConst v0) H1); inversion h''; auto.
  - inversion h'; subst; try congruence.
    + rewrite<- IHh1; auto.
    + assert (h39 := IHh2 _ H5); inversion h39.
  - inversion h'; subst; try congruence.
    + assert (h'' := IHh1 _ H6); inversion h''.
    + assert (VConst (S n) = VConst (S n0)) by auto.
      inversion H; subst; clear H.
      assert (v' = v'1) by auto; subst.
      auto.
Qed.

Lemma comp_expand : forall ty ectx t v,
    TmEval ectx t v -> Computable_tm ty ectx t -> Computable_val ty v.
Proof.
  induction ty; simpl.
  - firstorder.
    assert (v = x) by (eapply eval_det; eauto); subst.
    unfold Comp_Nat; eauto.
  - intros ? ? ? eval (t' & ectx' & eval' & comp).
    assert (v = VAbs t' ectx') by (eapply eval_det; eauto); subst; simpl.
    intros; auto.
Qed.

Lemma comp_norm : forall ty ectx t,
    Computable_tm ty ectx t -> exists v, TmEval ectx t v.
Proof.
  induction ty.
  - unfold Computable_tm.
    intros ? ? (v & eval & comp).
    eauto.
  - simpl.
    intros ? ? (t' & ectx' & eval' & _).
    eauto.
Qed.

Theorem well_typed_comp : forall Γ t ty,
 has_type Γ t ty ->
 forall ectx : eval_ctx,
   Computable_ctx Γ ectx ->
   Computable_tm ty ectx t
.
Proof.
  intros Γ t ty deriv.
  induction deriv; intros ectx h; simpl.
  - assert (exists v, nth ectx n v). (* Should be a lemma *)
    { revert n H;
        induction h; intros n h1.
      - inversion h1.
      - destruct n; [eexists; constructor |].
        inversion h1; subst; clear h1.
        edestruct IHh; eauto.
        eexists; constructor; eauto. }
    destruct H0 as (v & nth_v).
    eapply comp_eval; [repeat constructor; now eauto |].
    revert n v ty nth_v H.
    induction h.
    + intros ? ? ? h; inversion h.
    + intros n ? ?; destruct n.
      -- intros h1 h2; inversion h1; inversion h2; subst; auto.
      -- intros h1 h2; inversion h1; inversion h2; subst; eapply IHh; eauto.
  - exists t, ectx.
    split; [constructor |].
    intros; apply IHderiv.
    constructor; auto.
  - assert (ht := IHderiv1 _ h).
    assert (hu := IHderiv2 _ h).
    clear IHderiv2 IHderiv1.
    assert (hv := comp_norm _ _ _ ht).
    destruct hv as (v & eval_v).
    assert (hv := comp_expand _ _ _ _ eval_v ht).
    simpl in hv.
    destruct v; [| contradiction].
    assert (hv' := comp_norm _ _ _ hu).
    destruct hv' as (v' & eval_v').
    assert (hv' := comp_expand _ _ _ _ eval_v' hu).
    assert (hw := hv _ hv').
    assert (hw' := comp_norm _ _ _ hw).
    destruct hw' as (w & eval_w).
    apply comp_eval with (v := w).
    + econstructor; eauto.
    + eapply comp_expand; eauto.
  - exists (VConst n); split; econstructor; eauto.
  - edestruct IHderiv; eauto.
    destruct H as (eval_t & x_comp).
    inversion x_comp; subst.
    exists (VConst (S x0)); split; econstructor; auto.
  - simpl in IHderiv3.
    assert (IH1 := IHderiv1 _ h).
    assert (IH3 := IHderiv3 _ h).
    clear IHderiv1 IHderiv3.
    destruct IH3 as (v & eval_v & comp_v).
    destruct comp_v as (n & eq); subst.
    clear deriv3.
    revert t eval_v.
    induction n.
    + intros; assert (hvz := comp_norm _ _ _ IH1).
      destruct hvz as (vz & hz).
      apply comp_eval with (v := vz); [econstructor; eauto |].
      eapply comp_expand; eauto.
    + intros t eval_t.
      assert (IHn := IHn (TConst n) (Eval_0 _ _)).
      assert (hv_rev := comp_norm _ _ _ IHn).
      destruct hv_rev as (v & eval_v).
      assert (hw : Computable_tm A (v ::: VConst n ::: ectx) s).
      -- apply IHderiv2; repeat constructor; simpl; [| econstructor; now eauto| now auto].
         eapply comp_expand; eauto.
      -- assert (hw' := comp_norm _ _ _ hw). 
         destruct hw' as (w & eval_w).
         apply comp_eval with (v := w).
         { eapply Eval_recS; eauto. }
         {
           eapply comp_expand; eauto.
         }
Qed.


Theorem well_typed_eval : forall t, has_type Empty_ty_ctx t Nat -> exists v, Comp_Nat v /\ TmEval [::] t v.
Proof.
  intros t h.
  assert (h1 := well_typed_comp _ _ _ h).
  edestruct h1 as (v & h2 & h3); [constructor |].
  exists v; auto.
Qed.

Definition val_of_nat (n : nat) : value := VConst n.

Definition nat_of_val (v : value) : nat :=
  match v with
  | VConst n => n
  | _ => 0
  end.

Lemma retract_nat_of_val : forall v, Comp_Nat v -> val_of_nat (nat_of_val v) = v.
Proof.
  intros v h; destruct h; subst; auto.
Qed.

Inductive Nf (t : term) :=
  Nf_intro : forall n, TmEval [::] t (val_of_nat n) -> Nf t.


Theorem exists_nf : forall t, has_type Empty_ty_ctx t Nat -> exists (nf : Nf t), True.
Proof.
  intros t h.
  assert (h1 := well_typed_eval t h).
  destruct h1 as (v & comp & eval).
  rewrite <- retract_nat_of_val in eval; auto.
  exists (Nf_intro _ (nat_of_val v) eval).
  exact I.
Qed.

From Coq Require Import Logic.ConstructiveEpsilon.

Check constructive_indefinite_ground_description.

Print TmEval.
Print eval_ctx.
Print term.
Print type.



