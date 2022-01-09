(*

Ideas:
I'm borrowing generously from https://xavierleroy.org/talks/compilation-agay.pdf and
https://github.com/ajcave/code/blob/master/normalization/weak-head-bigstep-cbn.agda

But CBV.


*)


(* Trying to formalize the normalization of closed system F terms *)
Require Import List Arith Bool.

Import ListNotations.

Definition name := nat.

(* Don't really need de Bruijn for types: *)
(* We just do the "textbook logic book" trick and add a bunch of free var assumptions. *)
Inductive type :=
| Tvar : name -> type
| Arrow : type -> type -> type
| Forall : name -> type -> type.

Fixpoint is_free (n : name) (t : type) :=
  match t with
  | Tvar k => if k =? n then true else false
  | Arrow t1 t2 => (is_free n t1) || (is_free n t2)
  | Forall k t1 =>
    if n =? k then false else
      (is_free n t1)
  end.

(* Boring ol' shadowing substitution *)
Fixpoint ty_subst (n : name) (t u : type) :=
  match t with
  | Tvar k => if k =? n then u else Tvar k
  | Arrow t1 t2 => Arrow (ty_subst n t1 u) (ty_subst n t2 u)
  | Forall k t1 =>
    if n =? k then t else
    Forall k (ty_subst n t1 u)
  end.


(* No explicit type abstractions or applications: we don't really care about type-checking. *)
Inductive term :=
| Var : nat -> term
| App : term -> term -> term
| Abs : term -> term.

(* An evaluation context is either empty, or a pair of a term and an
eval context, with the remainder of the bindings. *)
Inductive eval_ctxt :=
| Empty_ctxt : eval_ctxt
| Push_ctxt : term -> eval_ctxt -> eval_ctxt -> eval_ctxt.

Notation "[::]" := Empty_ctxt.
Inductive value := VAbs : term -> eval_ctxt -> value.

Fixpoint nth_error (ectx : eval_ctxt) (n : nat) : option value :=
  match ectx with
  | Empty_ctxt => None
  | Push_ctxt t e cs =>
    match n with
    | 0 => Some (VAbs t e)
    | S m => nth_error cs m
    end
  end.

Definition cons_ctxt (v : value) (e : eval_ctxt) : eval_ctxt :=
  match v with
  | VAbs t e' => Push_ctxt t e' e
  end.

Notation "v ::: e" := (cons_ctxt v e)(at level 30, right associativity).

Inductive TmEval : eval_ctxt -> term -> value -> Prop :=
| Eval_var : forall ectx n v,
    nth_error ectx n = Some v ->
    TmEval ectx (Var n) v
(* Weak reduction *)
| Eval_abs : forall ectx t, TmEval ectx (Abs t) (VAbs t ectx)
(* Call by value *)
| Eval_app : forall ectx ectx' t t' u v v',
    TmEval ectx t (VAbs t' ectx') ->
    TmEval ectx u v ->
    TmEval (v ::: ectx') t' v' ->
    TmEval ectx (App t u) v'
.

Hint Constructors TmEval.

Definition context := list type.

Definition is_free_ctxt : name -> context -> bool :=
  fun n ctxt =>
    List.existsb (fun ty => is_free n ty) ctxt.

Fixpoint is_bound n ty :=
  match ty with
  | Tvar _ => false
  | Arrow ty1 ty2 =>
    is_bound n ty1 || is_bound n ty2
  | Forall m ty' =>
    (m =? n) || is_bound n ty'
  end.

(* true iff no bound variable if ty1 is free in ty2 *)
Definition no_capture ty1 ty2 :=
    forall n, is_bound n ty1 = true -> is_free n ty2 = false.


(* Type checking is undecidable, but who cares? *)
Inductive TyRel : context -> term -> type -> Prop :=
| TyRel_var : forall ctxt n ty,
    List.nth_error ctxt n = Some ty ->
    TyRel ctxt (Var n) ty
| TyRel_abs : forall ctxt ty1 ty2 t,
    TyRel (ty1::ctxt) t ty2 ->
    TyRel ctxt (Abs t) (Arrow ty1 ty2)
| TyRel_app : forall ctxt ty1 ty2 t u,
    TyRel ctxt t (Arrow ty1 ty2) ->
    TyRel ctxt u ty1 ->
    TyRel ctxt (App t u) ty2
| TyRel_ty_abs : forall ctxt n ty t,
    is_free_ctxt n ctxt = false ->
    TyRel ctxt t ty ->
    TyRel ctxt t (Forall n ty)
| TyRel_ty_app : forall ctxt n ty1 ty2 t,
    no_capture ty1 ty2 -> (* very required! *)
    TyRel ctxt t (Forall n ty1) ->
    TyRel ctxt t (ty_subst n ty1 ty2) (* No tags for substs, because they only matter operationally. *)
.

(* What we really care about: a term normalizes in a context. *)
Definition norm (ectx : eval_ctxt) (t : term) :=
  exists v, TmEval ectx t v.

(* We actually care about *pairs* of predicates, one for term (and
closures) and one for just values *)
Record comp_pair :=
  { comp_term : eval_ctxt -> term -> Prop;
    comp_val : value -> Prop }.

Definition valuation := name -> comp_pair.


Definition extend (f : valuation)(v : name)(P : comp_pair) : valuation :=
  fun var => if var =? v then P else f var.

(* This is the "usual" computability predicates stuff, but for normal forms in a given strategy.*)
Record computable (P : comp_pair) :=
  {
  comp_norm : forall ectx t, comp_term P ectx t -> norm ectx t;
  comp_val_of_term : forall ectx t v, TmEval ectx t v -> comp_term P ectx t -> comp_val P v;
  comp_term_of_val : forall ectx t v, TmEval ectx t v -> comp_val P v -> comp_term P ectx t
  }.

Definition norm_pred := {| comp_term := norm; comp_val := fun _ => True |}.

(* A good sanity check, but we use it for dummy values later *)
Lemma computable_norm : computable norm_pred.
Proof.
  constructor; simpl; auto.
  intros; eexists; eauto.
Qed.

(* Amusingly, we could probably use empty sets, and have a nice empty
interpretation for types without values, like Forall X.X...

The "usual" proof has neutral terms in all types.
*)

Hint Resolve computable_norm.

(* The usual interpretation of types in system F with computable predicates *)
(* Though this is the "positive" version, where a term at arrow type is computable
   iff its *values* are. *)
Fixpoint interp_term (ty : type) : valuation -> eval_ctxt -> term -> Prop :=
  fun val =>
    match ty with
    | Tvar v => comp_term (val v)
    | Arrow t1 t2 =>
      fun ectx t =>
        exists t' ectx',
          TmEval ectx t (VAbs t' ectx') /\
        forall v,
          interp_val t1 val v ->
          interp_term t2 val (v ::: ectx') t'
    | Forall name ty =>
      fun ectx t =>
        forall P, computable P -> interp_term ty (extend val name P) ectx t
    end
with interp_val (ty : type) : valuation -> value -> Prop :=
       fun val =>
         match ty with
         | Tvar v => comp_val (val v)
         | Arrow t1 t2 =>
           fun v =>
             match v with
             | VAbs t env =>
               forall v,
                 interp_val t1 val v ->
                 interp_term t2 val (v ::: env) t
             end
         | Forall name ty =>
           fun v =>
             forall P, computable P -> interp_val ty (extend val name P) v
         end
.

Definition computable_valuation (val : valuation) :=
  forall v, computable (val v).

Lemma computable_valuation_extend : forall n val P,
    computable_valuation val ->
    computable P -> computable_valuation (extend val n P).
Proof.
  unfold extend, computable_valuation.
  intros n ? ? ? ? m.
  case (m =? n); auto.
Qed.

Hint Resolve computable_valuation_extend.

(* Surprisingly useful. This is a bit sad, since we don't really want
   to rely on it in the non-deterministic setting, or if confluence
   fails. *)
Lemma eval_det : forall ectx t v v',
    TmEval ectx t v -> TmEval ectx t v' -> v = v'.
Proof.
  intros t ectx v v' H; revert v'; induction H; intros v2 H'; inversion H'; subst; auto; try congruence.
  assert (v = v0) by firstorder.
  subst v.
  assert (H2 : VAbs t' ectx' = VAbs t'0 ectx'0) by firstorder.
  inversion H2; subst.
  now auto.
Defined. (* We use this in the WF proofs *)

Hint Resolve eval_det.

(* The crucial Girard trick: interpretations satisfy the computability conditions. *)
Lemma computable_interp_term : forall ty val,
    computable_valuation val ->
    computable {| comp_term := interp_term ty val; comp_val := interp_val ty val |} .
Proof.
  induction ty.
  simpl; intros val H; constructor; simpl; intros; try (destruct (H n); now eauto).
  - intros; constructor; simpl.
    + intros ectx t [t' [ectx' [eval_t _]]].
      eexists; now eauto.
    + intros ectx t v eval_t [t' [ectx' [eval_t2 comp_t']]].
      assert (v = VAbs t' ectx') by eauto; subst.
      auto.
    + intros ectx t v; destruct v as [t' ectx']; intros eval_t comp_t'.
      eexists; now eauto.
  - intros; constructor; simpl.
    + pose (P := norm_pred).
      assert (h := computable_norm : computable P).
      intros ectx t comp_t.
      assert (comp_t1 := comp_t _ h).
      assert (comp_ext : computable_valuation (extend val n P)) by auto.
      assert (comp_t2 := IHty _ comp_ext).
      destruct comp_t2; simpl in *.
      now auto.
    + intros ectx t v eval_t h P comp_p.
      assert (h0 : computable_valuation (extend val n P)) by auto.
      assert (comp_ext := IHty _ h0).
      destruct comp_ext; simpl in *.
      now eauto.
    + intros ectx t v eval_t h P comp_p.
      assert (h0 : computable_valuation (extend val n P)) by auto.
      assert (comp_ext := IHty _ h0).
      destruct comp_ext; simpl in *.
      now eauto.
Qed.


Hint Resolve computable_interp_term.

Check nth_error.

Definition ctxt_val : valuation -> eval_ctxt -> context -> Prop :=
  fun val ectx ctx =>
    forall n ty,
      List.nth_error ctx n = Some ty ->
      exists v,
      nth_error ectx n = Some v /\
      interp_val ty val v.

(* The notion of equality for computable pairs. Probably we should use
   setoids here, a lot of pain later because of our laziness...*)
Definition equiv_comp_pair P P' :=
  (forall ectx t,
      comp_term P ectx t <-> comp_term P' ectx t)
  /\
  (forall v,
      comp_val P v <-> comp_val P' v)
.

Lemma equiv_comp_pair_sym : forall P P',
    equiv_comp_pair P P' -> equiv_comp_pair P' P.
Proof.
  intros P P'; unfold equiv_comp_pair; firstorder.
Qed.

Lemma equiv_comp_pair_refl : forall P,
    equiv_comp_pair P P.
Proof.
  intros P; unfold equiv_comp_pair; firstorder.
Qed.

Hint Resolve equiv_comp_pair_refl.

Lemma extend_equiv : forall val val' n P,
    (forall m, equiv_comp_pair (val m) (val' m)) ->
    forall k, equiv_comp_pair (extend val n P k) (extend val' n P k).
Proof.
  intros.
  unfold extend.
  destruct (k =? n); simpl; auto.
Qed.

Lemma ty_subst_ext : forall ty val val',
    (forall n, equiv_comp_pair (val n) (val' n)) ->
    (forall ectx t, interp_term ty val ectx t -> interp_term ty val' ectx t)
    /\
    (forall v, interp_val ty val v -> interp_val ty val' v).
Proof.
  induction ty; intros val val' H; split; simpl; intros; try apply H; auto.
  - destruct H0 as [t' [ectx' [eval_t comp_t]]].
    exists t', ectx'; split; auto.
    intros; eapply IHty2; [now auto | apply comp_t].
    eapply IHty1; intros; [apply equiv_comp_pair_sym; now auto| now auto].
  - destruct v; intros; eapply IHty2; eauto.
    apply H0.
    eapply IHty1; [intros; apply equiv_comp_pair_sym; eauto| now eauto].
  - eapply IHty; [intros; apply extend_equiv; eauto| now auto].
  - eapply IHty; [intros; apply extend_equiv; eauto| now auto].
Qed.

(* Crucial to deal with our lack of DB in types.
   You think you're simplifing your life at first...
*)
Lemma is_not_free_extend : forall ty n val P,
    is_free n ty = false ->
    (forall ectx t,
      interp_term ty val ectx t <->
      interp_term ty (extend val n P) ectx t)
    /\
    (forall v,
        interp_val ty val v <->
        interp_val ty (extend val n P) v)
.
Proof.
  induction ty; simpl; intros.
  - unfold extend; assert (eq := Nat.eqb_eq n n0).
    destruct (n =? n0); split; intros; try congruence; reflexivity; eauto.
  - rewrite orb_false_iff in *.
    destruct H.
    split; [split; intro h; destruct h as [t' [ectx' [h1 h2]]]; exists t', ectx'; split; eauto; intros v| ].
    + edestruct IHty1; edestruct IHty2; eauto.
      rewrite<- H3.
      rewrite<- H2.
      eauto.
    + edestruct IHty1; edestruct IHty2; eauto.
      rewrite H3.
      rewrite H2.
      eauto.
    + intros v; destruct v.
      split; intros h v; edestruct IHty1; edestruct IHty2; eauto.
      -- rewrite<- H2.
         rewrite<- H3.
         eauto.
      -- rewrite H2.
         rewrite H3.
         now eauto.
  - assert (eq := Nat.eqb_eq n0 n).
    destruct (n0 =? n).
    assert (n0 = n) by firstorder; subst.
    + assert (forall P0 k,
                 equiv_comp_pair
                   (extend val n P0 k)
                   (extend (extend val n P) n P0 k)).
      {
        unfold extend; intros; destruct (k =? n); simpl;
          apply equiv_comp_pair_refl; eauto.
      }
      split; split; intros; eapply ty_subst_ext; intros;
        try apply H0; try (apply equiv_comp_pair_sym; apply H0); try apply H1; eauto. (* Maybe first [apply ...] here? *)
    + assert (forall P0 k,
                 equiv_comp_pair
                   (extend (extend val n0 P) n P0 k)
                   (extend (extend val n P0) n0 P k)).
      {
        unfold extend; intros.
        assert (eq' := Nat.eqb_eq k n).
        assert (eq'' := Nat.eqb_eq k n0).
        destruct (k =? n); destruct (k =? n0); simpl; try apply equiv_comp_pair_refl.
        assert (n0 = n) by (firstorder; congruence).
        exfalso.
        assert (false = true) by (apply eq; eauto).
        congruence.
      }
      split; split; intros;
        try (eapply ty_subst_ext; intros;
             apply equiv_comp_pair_sym; apply H0; apply IHty; now eauto).
      -- eapply ty_subst_ext; intros; try apply equiv_comp_pair_sym; try apply H0.
         apply IHty; eauto.
      -- assert (interp_term ty (extend (extend val n P0) n0 P) ectx t) by (eapply ty_subst_ext; intros; try apply H0; eauto).
         revert H3.
         apply IHty; eauto.
      -- eapply ty_subst_ext; intros; try apply equiv_comp_pair_sym; try apply H0; eauto.
         apply IHty; eauto.
      -- assert (interp_val ty (extend (extend val n P0) n0 P) v) by (eapply ty_subst_ext; intros; try apply H0; eauto).
         revert H3.
         apply IHty; eauto.
         (* WTF *)
         Unshelve.
         auto.
         auto.
         auto.
         auto.
         auto.
         auto.
         auto.
         auto.
Qed.


Lemma no_capture_arrow1 : forall ty1_1 ty1_2 ty2, no_capture (Arrow ty1_1 ty1_2) ty2 -> no_capture ty1_1 ty2.
Proof.
  unfold no_capture; simpl.
  setoid_rewrite orb_true_iff; auto.
Qed.

Hint Resolve no_capture_arrow1.

Lemma no_capture_arrow2 : forall ty1_1 ty1_2 ty2, no_capture (Arrow ty1_1 ty1_2) ty2 -> no_capture ty1_2 ty2.
Proof.
  unfold no_capture; simpl.
  setoid_rewrite orb_true_iff; auto.
Qed.

Hint Resolve no_capture_arrow2.

Lemma no_capture_forall : forall n ty1 ty2, no_capture (Forall n ty1) ty2 -> no_capture ty1 ty2.
Proof.
  unfold no_capture; simpl.
  setoid_rewrite orb_true_iff; auto.
Qed.

Hint Resolve no_capture_forall.

Lemma no_capture_forall_free : forall n ty1 ty2,
    no_capture (Forall n ty1) ty2 ->
    is_free n ty2 = false.
Proof.
  unfold no_capture; intros n ty1 ty2 H; generalize (H n); simpl.
  rewrite Nat.eqb_refl; simpl; auto.
Qed.

Hint Resolve no_capture_forall_free.

(* And the magical lemma to swap substitution and interpretation. Also painful. *)
Lemma ty_subst_extend : forall ty1 n ty2 val,
    let interp_ty2 := {| comp_term := interp_term ty2 val; comp_val := interp_val ty2 val |} in
    no_capture ty1 ty2 ->
    (forall ectx t, interp_term (ty_subst n ty1 ty2) val ectx t <-> interp_term ty1 (extend val n interp_ty2) ectx t)
    /\
    (forall v, interp_val (ty_subst n ty1 ty2) val v <-> interp_val ty1 (extend val n interp_ty2) v)
.
Proof.
  induction ty1; unfold extend in *; simpl; intros m; intros.
  - simpl; destruct (n =? m); now auto.
  - split; split; intros h.
    + destruct h as [t' [ectx' [eval_t comp_t]]].
      exists t', ectx'; split; auto; intros v0.
      intros.
      apply IHty1_2; eauto.
      apply comp_t.
      apply IHty1_1; eauto.
    + destruct h as [t' [ectx' [eval_t comp_t]]].
      exists t', ectx'; split; auto.
      intros; apply IHty1_2; eauto.
      apply comp_t.
      apply IHty1_1; eauto.
    + destruct v; intros v comp_v.
      apply IHty1_2; eauto.
      apply h.
      apply IHty1_1; eauto.
    + destruct v; intros v comp_v.
      apply IHty1_2; eauto.
      apply h.
      apply IHty1_1; eauto.
  - simpl; unfold extend.
    case_eq (m =? n); intros eq_n_m; try rewrite eq_n_m; simpl;
      [assert (m = n) by (apply beq_nat_true; eauto)  | assert (m <> n) by (apply beq_nat_false; eauto)];
      [subst; unfold extend; split; intros; split; intros;
        assert
          (val_ext : forall n m,
              equiv_comp_pair
                ((fun var : name =>
                    if var =? n
                    then P else val var) m)
                ((fun var : name =>
                    if var =? n
                    then P
                    else if var =? n then {| comp_term := interp_term ty2 val; comp_val := interp_val ty2 val |} else val var) m)
          ) by (intros k1 k2; destruct (k2 =? k1); eauto);
        eapply ty_subst_ext; eauto; try apply val_ext; intros; try (apply equiv_comp_pair_sym; apply val_ext) |].
    split; split; intros; assert (IH := IHty1 m ty2 (extend val n P)); clear IHty1; unfold extend in *.
    + apply (ty_subst_ext
               ty1
               (
                 fun var : name =>
                   if var =? m
                   then
                     {|
                       comp_term := interp_term ty2 (fun var0 : name => if var0 =? n then P else val var0);
                       comp_val := interp_val ty2 (fun var0 : name => if var0 =? n then P else val var0) |}
                   else if var =? n then P else val var
               )
               _); [| apply IH; eauto].
      intros.
      assert (at_most_one : ((n0 =? m) = false) \/ ((n0 =? n) = false)) by
          (case_eq (n0 =? m); case_eq (n0 =? n);
           repeat rewrite Nat.eqb_neq;
           repeat rewrite Nat.eqb_eq;
           intros; try congruence; auto).
      split; intros; destruct (n0 =? m); destruct (n0 =? n); simpl; try reflexivity; destruct at_most_one; try congruence.
      -- symmetry; eapply is_not_free_extend; eauto.
      -- symmetry; eapply is_not_free_extend; eauto.
    + apply IH; [ now eauto |].
      apply (ty_subst_ext
               ty1
               (
                 fun var : name =>
                   if var =? n
                   then P
                   else if var =? m then {| comp_term := interp_term ty2 val; comp_val := interp_val ty2 val |} else val var
               )
               _); [ | now auto].
      intros n0;
      assert (at_most_one : ((n0 =? m) = false) \/ ((n0 =? n) = false)) by
          (case_eq (n0 =? m); case_eq (n0 =? n);
           repeat rewrite Nat.eqb_neq;
           repeat rewrite Nat.eqb_eq;
           intros; try congruence; auto).
      split; intros; destruct (n0 =? m); destruct (n0 =? n); simpl; try reflexivity; destruct at_most_one; try congruence.
      -- eapply is_not_free_extend; eauto.
      -- eapply is_not_free_extend; eauto.
    + apply (ty_subst_ext
               ty1
               (
                 fun var : name =>
                   if var =? m
                   then
                     {|
                       comp_term := interp_term ty2 (fun var0 : name => if var0 =? n then P else val var0);
                       comp_val := interp_val ty2 (fun var0 : name => if var0 =? n then P else val var0) |}
                   else if var =? n then P else val var
               )
               _); [| apply IH; eauto].
      intros.
      assert (at_most_one : ((n0 =? m) = false) \/ ((n0 =? n) = false)) by
          (case_eq (n0 =? m); case_eq (n0 =? n);
           repeat rewrite Nat.eqb_neq;
           repeat rewrite Nat.eqb_eq;
           intros; try congruence; auto).
      split; intros; destruct (n0 =? m); destruct (n0 =? n); simpl; try reflexivity; destruct at_most_one; try congruence.
      -- symmetry; eapply is_not_free_extend; eauto.
      -- symmetry; eapply is_not_free_extend; eauto.
    + apply IH; [now eauto |].
      apply (ty_subst_ext
               ty1
               (
                 fun var : name =>
                   if var =? n
                   then P
                   else if var =? m then {| comp_term := interp_term ty2 val; comp_val := interp_val ty2 val |} else val var
               )
               _); [| now eauto].
      intros;
      assert (at_most_one : ((n0 =? m) = false) \/ ((n0 =? n) = false)) by
          (case_eq (n0 =? m); case_eq (n0 =? n);
           repeat rewrite Nat.eqb_neq;
           repeat rewrite Nat.eqb_eq;
           intros; try congruence; auto).
      split; intros; destruct (n0 =? m); destruct (n0 =? n); simpl; try reflexivity; destruct at_most_one; try congruence;
        eapply is_not_free_extend; eauto.
Qed.

Definition interp_pair ty val :=
  {| comp_term := interp_term ty val; comp_val := interp_val ty val |}.

Lemma comp_eval : forall P ectx ectx' t t',
    computable P ->
    (forall v, TmEval ectx' t' v -> TmEval ectx t v) ->
    comp_term P ectx' t' -> comp_term P ectx t.
Proof.
  intros.
  destruct H.
  destruct (comp_norm0 ectx' t' H1) as [v eval'].
  apply comp_term_of_val0 with (v := v); auto.
  eapply comp_val_of_term0; now eauto.
Qed.

Lemma is_free_ctx_nth_error : forall n m ctx ty,
    is_free_ctxt n ctx = false ->
    List.nth_error ctx m = Some ty ->
    is_free n ty = false.
Proof.
  unfold is_free_ctxt.
  intros.
  assert (is_free n (nth m ctx (Tvar n)) = false).
  {
    apply existsb_nth; auto.
    apply nth_error_Some; congruence.
  }
  assert (nth m ctx (Tvar n) = ty) by (apply nth_error_nth; auto).
  subst; auto.
Qed.

Lemma ctxt_val_extend : forall P n val ectx ctx,
    is_free_ctxt n ctx = false ->
    computable P -> ctxt_val val ectx ctx ->
    ctxt_val (extend val n P) ectx ctx.
Proof.
  unfold ctxt_val.
  intros ? ? ? ? ? ? ? h n ty ?.
  edestruct h as [v [nth_v interp_v]]; eauto.
  exists v; split; auto.
  apply is_not_free_extend; auto.
  eapply is_free_ctx_nth_error; eauto.
Qed.

(* Somewhat painless once you get *everything perfectly right* up to here. *)
Theorem ty_safe : forall ctx t ty ectx val,
    computable_valuation val ->
    TyRel ctx t ty ->
    ctxt_val val ectx ctx ->
    interp_term ty val ectx t.
Proof.
  intros ctx t ty ectx val val_comp H; revert ectx val val_comp; induction H; simpl; intros; auto.
  - pose (P := {| comp_term := interp_term ty val; comp_val := interp_val ty val |}).
    assert (comp_ty : computable (interp_pair ty val)) by (unfold interp_pair; auto).
    destruct comp_ty.
    edestruct H0 as [v [lookup_v comp_v]]; eauto.
    simpl in *.
    eapply comp_term_of_val0; now eauto.
  - exists t, ectx; split; [now auto|intros].
    apply IHTyRel; [now auto|].
    intros n; destruct n; simpl.
    + intros ty eq; inversion eq; subst.
      destruct v.
      unfold ":::"; simpl.
      exists (VAbs t0 e); split; now auto.
    + intros ty; simpl.
      intros eq.
      edestruct H0 as [v' [lookup_v' comp_v']]; eauto.
      exists v'; unfold ":::"; destruct v; simpl; now auto.
  - simpl in *.
    edestruct IHTyRel1 as [t' [ectx' [eval_t comp_t]]]; eauto.
    assert (comp_ty1 : computable (interp_pair ty1 val)) by (unfold interp_pair; auto).
    assert (comp_ty2 : computable (interp_pair ty2 val)) by (unfold interp_pair; auto).
    destruct comp_ty1; destruct comp_ty2; simpl in *.
    assert (norm_u : norm ectx u) by auto.
    destruct norm_u as [v eval_u].
    assert (comp_red_t_u : interp_term ty2 val (v ::: ectx') t') by (eapply comp_t; eauto).
    apply (comp_eval (interp_pair ty2 val)) with (ectx' := (v ::: ectx'))(t' := t'); unfold interp_pair; simpl; auto.
    intros; now eauto.
  - apply IHTyRel; eauto.
    apply ctxt_val_extend; auto.
  - simpl in *.
    apply ty_subst_extend; auto.
Qed.

(* Easy peesy. We do use the fact that there is *some* computable predicate. *)
Theorem norm_f : forall t ty,
    TyRel [] t ty ->
    norm [::] t.
Proof.
  intros.
  pose (val := fun _ : name => norm_pred).
  assert (interp_term ty val [::] t).
  - apply ty_safe with (ctx := []); auto.
    + intro; simpl; apply computable_norm.
    + intro n; destruct n; simpl; intros; congruence.
  - assert (comp : computable (interp_pair ty val))
      by (unfold interp_pair; apply computable_interp_term; intro; simpl; apply computable_norm).
    destruct comp; auto.
Qed.

(* Sadly, in a constructive logic, this isn't quite enough to get you a *normalization function*. *)
(* Let's finish the steps, which involve Acc, well_founded and singleton elimination... *)

(* The exact things we need for the recursive calls: this is roughly the Bove-Capretta method. *)
Inductive TmEvalRel : forall (cl1 cl2 : (eval_ctxt * term)), Prop :=
| TmEvalRel_appl : forall e t u,
    TmEvalRel (e, t) (e, App t u)
| TmEvalRel_appr : forall e t u,
    TmEvalRel (e, u) (e, App t u)
| TmEvalRel_hd : forall e e' t t' u v,
    TmEval e t (VAbs t' e') ->
    TmEval e u v ->
    TmEvalRel (v ::: e', t') (e, App t u).

Hint Constructors TmEvalRel.

(* Well-founded by construction of the evaluation tree *)
Theorem acc_tmeval : forall e t v,
    TmEval e t v ->
    Acc TmEvalRel (e, t).
Proof.
  intros e t v h; induction h; constructor; intros [e1 t1] lt_t_t1;
    inversion lt_t_t1; subst; try congruence.
  assert (v = v0) by eauto; subst. (* this is kind of a hack to enable turning existentials into deterministic computations *)
  assert (h : VAbs t' ectx' = VAbs t1 e') by eauto.
  inversion h; subst.
  auto.
Defined. (* Just in case we wanna compute a bit *)

(* We actually know how to define a WF relation on *these* now. *)
Record red_triple :=
  {
  red_ctx : eval_ctxt;
  red_tm : term;
  red_correct : exists val, TmEval red_ctx red_tm val;
  }.

Definition eval_rel : red_triple -> red_triple -> Prop :=
  fun tr1 tr2 =>
    let ectx1 := red_ctx tr1 in
    let ectx2 := red_ctx tr2 in
    let t1 := red_tm tr1 in
    let t2 := red_tm tr2 in
    TmEvalRel (ectx1, t1) (ectx2, t2).

(* We need a few lemmas from here if we're to prove anything... *)
Require Import Wellfounded.

Theorem wf_triple : well_founded eval_rel.
Proof.
  intros [ectx t [v red_v]].
  constructor.
  intros [ectx_y t_y [v_y red_v_y]]; unfold eval_rel; simpl.
  intros; eapply Acc_lemma; [ | reflexivity].
  simpl.
  eapply acc_tmeval; eauto.
Defined.

(* Gotta be reaaaal careful here to get a nice-lookign term *)
Definition eval_triple : forall tr : red_triple, { v : value | TmEval (red_ctx tr) (red_tm tr) v }.
  apply (Fix wf_triple).
  intros x eval_triple_rec.
  destruct x as [ectx t ?].
  destruct t.
  (* Variable case *)
  - case_eq (nth_error ectx n); intros.
    + exists v; simpl.
      destruct red_correct0.
      inversion t; subst.
      constructor; auto.
    + (* Can't happen because we have *some* value. *)
      exfalso.
      destruct red_correct0.
      inversion t; congruence.
  - (* evaluate t1 *)
    assert (val_t1 : { v | TmEval ectx t1 v }).
    + refine (eval_triple_rec {| red_ctx := ectx; red_tm := t1; red_correct := _ |} _ ).
      unfold eval_rel; simpl.
      eauto. (* Auto is ok here because we're in prop *)
    + (* evaluate t2 *)
      assert (val_t2 : { v | TmEval ectx t2 v} ).
      -- refine (eval_triple_rec {| red_ctx := ectx; red_tm := t2; red_correct := _ |} _ ).
         unfold eval_rel; simpl.
         eauto.
      -- simpl.
         destruct val_t1 as [[t1' ectx'] h1].
         destruct val_t2 as [v2 h2].
         assert (val_app : { v | TmEval (v2 ::: ectx') t1' v }).
         ++ refine (eval_triple_rec {| red_ctx := v2 ::: ectx'; red_tm := t1'; red_correct := _ |} _).
            unfold eval_rel; simpl; eauto.
         ++ destruct val_app as [v' h_app].
            exists v'; eauto.
  - exists (VAbs t ectx); unfold eval_rel; simpl; auto.
    Unshelve.
    destruct red_correct0; inversion t; eexists; eauto.
    destruct red_correct0; inversion t; eexists; eauto.
    destruct red_correct0; inversion t; subst.
    exists x.
    assert (v = v2) by eauto; subst.
    assert (h : VAbs t1' ectx' = VAbs t' ectx'0) by eauto; inversion h; subst.
    auto.
Defined.


Definition eval_f (t : term) (ty : type)(well_typed : TyRel [] t ty) : value :=
  let triple := {| red_ctx := [::]; red_tm := t; red_correct := norm_f t ty well_typed |} in
  let v := eval_triple triple in
  proj1_sig v.

Theorem eval_f_correct : forall t ty wt,
    TmEval [::] t (eval_f t ty wt).
Proof.
  unfold eval_f.
  intros.
  pose (v := (eval_triple {| red_ctx := [::]; red_tm := t; red_correct := norm_f t ty wt |})).
  assert (h := @proj2_sig _ _ v).
  simpl in h.
  apply h.
Qed.

(* Just to see what it's like *)
Recursive Extraction eval_f.
(* Amusingly this gives an evaluator for *any* term! Only guarenteed to terminate on well-typed ones... *)
(* It would be nice to get better extraction for evaluation contexts,
   say to arrays, so that we could actually get a somewhat decent
   evaluator. Left as exercise to the reader. *)
