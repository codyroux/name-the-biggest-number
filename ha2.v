(* A relatively straightforward formalization of HA^2 *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Inductive tm :=
| v(name : string)
| Succ(a : tm)
| Z
| Plus(a b : tm)
| Times(a b : tm)
.

Inductive pred :=
(* Just unary predicates? *)
| Atom : string -> tm -> pred
(* Quantification over terms *)
| Forallt : string -> pred -> pred
(* Quantification over terms *)
| ForallP : string -> pred -> pred
| Impl : pred -> pred -> pred.

Notation "P ⇒ Q" := (Impl P Q)(at level 30, right associativity).

Notation "t ∈ X" := (Atom X t)(at level 20, no associativity).

Notation "'FORALL' X , P" := (ForallP X P)(at level 33).
Notation "'all' x , P" := (Forallt x P) (at level 33).

Check (all "foo", v"foo" ∈ "Bar" ⇒ v"foo" ∈ "Bar").

Definition PVal := string -> nat -> Prop.

Definition VVal := string -> nat.

Check string_dec.

Definition extend{A} (f : string -> A) : string -> A -> (string -> A) :=
  fun s a s' =>
    if string_dec s s' then
      a
    else
      f s'.

Fixpoint eval_tm (vval : VVal) (t : tm) : nat :=
  match t with
  | v x => vval x
  | Succ t => S (eval_tm vval t)
  | Z => 0
  | Plus t1 t2 => (eval_tm vval t1) + (eval_tm vval t2)
  | Times t1 t2 => (eval_tm vval t1) * (eval_tm vval t2)
  end.

Fixpoint eval (pval : PVal) (vval : VVal) (P : pred) : Prop :=
  match P with
  | t ∈ X => (pval X) (eval_tm vval t)
  | all x, P => forall n, eval pval (extend vval x n) P
  | FORALL X, P => forall Pr, eval (extend pval X Pr) vval P
  | P ⇒ Q => (eval pval vval P) -> (eval pval vval Q)
  end.

Import ListNotations.

Definition ctxt := list pred.

Search (string -> string -> bool).

Fixpoint free_pred_var (name : string) (P : pred) : bool :=
  match P with
  | _ ∈ X => eqb name X
  | all x, P => free_pred_var name P
  | FORALL X, P =>
      if string_dec name X then
        false
      else free_pred_var name P
  | P ⇒ Q => (free_pred_var name P) || (free_pred_var name Q)
  end
.

Fixpoint free_tm_var_tm (name : string) (t : tm) : bool :=
  match t with
  | v x => eqb x name
  | Succ t => free_tm_var_tm name t
  | Z => false
  | Plus t1 t2 => (free_tm_var_tm name t1) || (free_tm_var_tm name t2)
  | Times t1 t2 => (free_tm_var_tm name t1) || (free_tm_var_tm name t2)
  end.

Fixpoint free_tm_var (name : string) (P : pred) : bool :=
  match P with
  | t ∈ _ => free_tm_var_tm name t
  | all x, P =>
      if string_dec name x then
        false
      else free_tm_var name P
  | FORALL X, P => free_tm_var name P
  | P ⇒ Q => (free_tm_var name P) || (free_tm_var name Q)
  end
.


Fixpoint bound_tm_var (name : string) (P : pred) : bool :=
  match P with
  | _ ∈ _ => false
  | all x, P => eqb x name || (bound_tm_var name P)
  | FORALL X, P => bound_tm_var name P
  | P ⇒ Q => (bound_tm_var name P) || (bound_tm_var name Q)
  end.

Fixpoint bound_pred_var (name : string) (P : pred) : bool :=
  match P with
  | _ ∈ _ => false
  | all x, P => bound_pred_var name P
  | FORALL X, P => (eqb X name) || bound_pred_var name P
  | P ⇒ Q => (bound_pred_var name P) || (bound_pred_var name Q)
  end.
  

Definition no_capture_tm (P : pred) (t : tm) : Prop :=
  forall x, bound_tm_var x P = true -> free_tm_var_tm x t = false.

Definition no_capture_prop (P : pred) (Q : pred) : Prop :=
  (* We need a bunch of these conditions to avoid capture *)
  (forall x, bound_tm_var x P = true -> bound_tm_var x Q = false)
  /\
    (forall x, bound_tm_var x Q = true -> free_tm_var x P = false)
  /\
    (forall x, bound_tm_var x P = true -> free_tm_var x Q = false)
  /\
    (* We only need this direction for predicate variables, since they
       can't be free in terms. *)
    (forall X, bound_pred_var X P = true -> free_pred_var X P = false)
.

Search (list _ -> bool).

Definition free_pred name Γ := existsb (free_pred_var name) Γ.
Definition free_tm name Γ := existsb (free_tm_var name) Γ.

Fixpoint subst_tm_tm (t : tm) (x : string)(u : tm) :=
  match t with
  | v y => if string_dec x y then u else v y
  | Succ t => Succ (subst_tm_tm t x u)
  | Z => Z
  | Plus t1 t2 => Plus (subst_tm_tm t1 x u) (subst_tm_tm t2 x u)
  | Times t1 t2 => Times (subst_tm_tm t1 x u) (subst_tm_tm t2 x u)
  end.

Fixpoint subst_tm_pred (P : pred)(x : string)(u : tm) :=
  match P with
  | t ∈ X => subst_tm_tm t x u ∈ X
  | all y, P =>
      if string_dec x y then all y, P else all y, (subst_tm_pred P x u)
  | FORALL X, P => FORALL X, (subst_tm_pred P x u)
  | P ⇒ Q => (subst_tm_pred P x u) ⇒ (subst_tm_pred Q x u)
  end.

(* We'll use this to abstract over terms in predicates *)
Definition pattern_var : string := "_".

(* This is where we'll get full 2nd order comprehension *)
Fixpoint subst_pred_pred (P : pred)(X : string)(Q : pred) :=
  match P with
  | t ∈ Y => if string_dec X Y then subst_tm_pred Q pattern_var t else P
  | all y, P => all y, (subst_pred_pred P X Q)
  | FORALL Y, P =>
      if string_dec X Y then FORALL Y, P
      else  FORALL Y, (subst_pred_pred P X Q)
  | P1 ⇒ P2 => (subst_pred_pred P1 X Q) ⇒ (subst_pred_pred P2 X Q)
  end.

Notation "x # Γ" := (free_tm x Γ = false)(at level 30).
Notation "X ## Γ" := (free_pred X Γ = false)(at level 30).

Definition P : string := "P".
Definition x : string := "x".
Definition y : string := "y".

Notation "t1 ≃ t2" := (FORALL P, t1 ∈ P ⇒ t2 ∈ P) (at level 20).

Notation "∃ y , Q" := (FORALL P, (all y, Q ⇒ P) ⇒ P)(at level 10).

Check In.

Locate "=".

Notation "⊥" := (FORALL P, all y, v y ∈ P).

Inductive derives : ctxt -> pred -> Prop :=
| axiom : forall Γ P, In P Γ -> derives Γ P
| imp_intro : forall Γ P Q, derives (P::Γ) Q -> derives Γ (P ⇒ Q)
| forallt_intro : forall Γ x P, x # Γ -> derives Γ P -> derives Γ (all x, P)
| forallP_intro : forall Γ X P, X ## Γ -> derives Γ P -> derives Γ (FORALL X, P)
| imp_elim : forall Γ P Q, derives Γ (P ⇒ Q) -> derives Γ P -> derives Γ Q
| forallt_elim : forall Γ P x t,
    no_capture_tm P t ->
    derives Γ (all x, P) -> derives Γ (subst_tm_pred P x t)
| forallP_elim : forall Γ P X Q,
    no_capture_prop P Q ->
    derives Γ (FORALL X, P) -> derives Γ (subst_pred_pred P X Q)
| zero_S : forall Γ, derives Γ (all y, Succ (v y) ≃ Z ⇒ ⊥)
| inj_S : forall Γ,
    derives Γ (all x, all y, (Succ (v x)) ≃ (Succ (v y)) ⇒ (v x ≃ v y))
| plus_Z : forall Γ, derives Γ (all x, Plus (v x) Z ≃ v x)
| plus_S : forall Γ,
    derives Γ (all x, all y, Plus (v x) (Succ (v y)) ≃ Succ (Plus (v x) (v y)))
| times_Z : forall Γ, derives Γ (all x, Times (v x) Z ≃ Z)
| times_S : forall Γ,
    derives Γ (all x, all y, Times (v x) (Succ (v y)) ≃ (Plus (v x) (Times (v x) (v y))))
| ind : forall Γ,
    derives Γ (FORALL P, Z ∈ P ⇒ (all x, v x ∈ P ⇒ (Succ (v x)) ∈ P) ⇒ all x, v x ∈ P)
.


Notation "Γ ⊢ P" := (derives Γ P)(at level 40).

Search (list _ -> Prop).

Definition validates(pval : PVal)(vval : VVal) (Γ : ctxt) : Prop :=
  Forall (eval pval vval) Γ.

Definition models (Γ : ctxt)(P : pred) : Prop :=
  forall pval vval,
    validates pval vval Γ -> eval pval vval P.

Notation "Γ ⊧ P" := (models Γ P)(at level 40).

Lemma extend_subst_tm : forall t vval x u n,
    eval_tm vval u = n ->
    eval_tm vval (subst_tm_tm t x u) = eval_tm (extend vval x n) t.
Proof.
  induction t; intros; simpl; auto.
  unfold extend.
  destruct (string_dec x0 name); subst; auto.
Qed.

Lemma eval_tm_ext : forall t vval vval',
    (forall x, vval x = vval' x) ->
    eval_tm vval t = eval_tm vval' t.
Proof.
  induction t; intros; simpl; auto.
Qed.

Lemma eval_ext : forall P pval vval vval',
    (forall x, vval x = vval' x) ->
    eval pval vval P <-> eval pval vval' P.
Proof.
  induction P0; intros; simpl.
  - erewrite eval_tm_ext; eauto; reflexivity.
  - split; intros; eapply IHP0.
    + intros; unfold extend.
      rewrite<- H.
      reflexivity.
    + now eauto.
    + intros; unfold extend; rewrite H; reflexivity.
    + now eauto.
  - split; intros; eapply IHP0.
    + intros; symmetry; now apply H.
    + now apply H0. (* Huh, some eta here... *)
    + now apply H.
    + now auto.
  - rewrite IHP0_1 in *; try apply H.
    rewrite IHP0_2 in *; try apply H.
    reflexivity.
Qed.


Lemma eval_ext' : forall P pval pval' vval,
    (forall X, pval X = pval' X) ->
    eval pval vval P <-> eval pval' vval P.
Proof.
  induction P0; intros; simpl.
  - erewrite H; reflexivity.
  - split; intros; eapply IHP0.
    + intros; symmetry; now eauto.
    + now auto.
    + now eauto.
    + now eauto.
  - split; intros h Pr.
    + eapply IHP0; [| apply h].
      intros; unfold extend.
      destruct (string_dec s X); now eauto.
    + eapply IHP0; [| apply h].
      intros; unfold extend.
      destruct (string_dec s X); now eauto.
  - rewrite IHP0_1; eauto.
    rewrite IHP0_2; eauto.
    reflexivity.
Qed.


Lemma extend_commut : forall A s1 s2 a b (f : string -> A),
    s1 <> s2 ->
    forall s, extend (extend f s2 b) s1 a s = extend (extend f s1 a) s2 b s.
Proof.
  intros.
  unfold extend.
  destruct (string_dec s1 s);
    destruct (string_dec s2 s); congruence.
Qed.

Lemma extend_idem : forall A s1 s2 a b (f : string -> A),
    s1 = s2 ->
    forall s, extend (extend f s2 b) s1 a s = extend f s1 a s.
Proof.
  unfold extend.
  intros.
  destruct (string_dec s1 s); auto.
  destruct (string_dec s2 s); auto.
  congruence.
Qed.

Search "_ || _".

Lemma no_capture_tm_forall : forall P x t,
    no_capture_tm (all x, P) t -> no_capture_tm P t.
Proof.
  unfold no_capture_tm; simpl; intros.
  apply H.
  apply Bool.orb_true_intro; right; auto.
Qed.

Lemma no_capture_tm_imp_l : forall P Q t,
    no_capture_tm (P ⇒ Q) t -> no_capture_tm P t.
Proof.
  unfold no_capture_tm; simpl; intros; apply H.
  apply Bool.orb_true_intro; auto.
Qed.

Lemma no_capture_tm_imp_r : forall P Q t,
    no_capture_tm (P ⇒ Q) t -> no_capture_tm Q t.
Proof.
  unfold no_capture_tm; simpl; intros; apply H.
  apply Bool.orb_true_intro; auto.
Qed.

Hint Resolve no_capture_tm_imp_l no_capture_tm_imp_r.

Lemma nfree_tm_extend_tm : forall t vval x n,
    free_tm_var_tm x t = false ->
    eval_tm vval t = eval_tm (extend vval x n) t.
Proof.
  induction t; simpl; auto;
    intros vval s n.
  - unfold extend; destruct (string_dec s name); subst; [| now auto].
    rewrite eqb_refl; congruence.
  - rewrite Bool.orb_false_iff.
    intros [h1 h2].
    now eauto.
  - rewrite Bool.orb_false_iff.
    intros [h1 h2].
    now eauto.
Qed.


Lemma nfree_tm_extend_pred : forall P pval vval x n,
    free_tm_var x P = false ->
    eval pval vval P <-> eval pval (extend vval x n) P.
Proof.
  induction P0; simpl; intros.
  - erewrite <- nfree_tm_extend_tm; now auto.
  - split; intros h n'; destruct (string_dec x0 s); subst; auto.
    + eapply eval_ext; [apply extend_idem; now auto| now auto].
    + eapply eval_ext; [apply extend_commut; now auto|].
      apply IHP0; now auto.
    + assert (h' := h n'); clear h.
      erewrite eval_ext in h'; [| eapply extend_idem; now auto].
      auto.
    + assert (h' := h n'); clear h.
      erewrite eval_ext in h'; [| eapply extend_commut; now auto].
      eapply IHP0; eauto.
  - split; intros Pr h.
    + apply IHP0; now auto.
    + eapply IHP0; now auto.
  - rewrite Bool.orb_false_iff in H; destruct H as [h1 h2].
    erewrite IHP0_1; eauto.
    erewrite IHP0_2; eauto.
    reflexivity.
Qed.

Lemma nfree_pred_extend_pred : forall P pval vval X Q,
    free_pred_var X P = false ->
    eval pval vval P <-> eval (extend pval X Q) vval P.
Proof.
  induction P0; simpl; intros.
  - unfold extend.
    destruct string_dec; subst; try rewrite eqb_refl in *; try congruence.
    reflexivity.
  - split; intros h n'.
    + erewrite<- IHP0; now eauto.
    + erewrite IHP0; now eauto.
  - split; intros Pr h; destruct (string_dec X s); subst; auto.
    +  eapply eval_ext'; [apply extend_idem; now auto| now auto].
    + eapply eval_ext'; [apply extend_commut; now auto|].
      apply IHP0; auto.
    + assert (h' := Pr h).
      eapply eval_ext' in h';
        [eapply h' | ].
      intros; erewrite extend_idem; now eauto.
    + rewrite IHP0; [| eauto].
      eapply eval_ext'; [apply extend_commut; now auto|].
      now eauto.
  - rewrite Bool.orb_false_iff in H; destruct H as [h1 h2].
    erewrite IHP0_1; eauto.
    erewrite IHP0_2; eauto.
    reflexivity.
Qed.
  

Lemma no_capture_tm_forall_extend : forall x P u t vval,
    no_capture_tm (all x, P) t ->
    eval_tm vval t = eval_tm (extend vval x u) t.
Proof.
  unfold no_capture_tm; simpl.
  intros x P u; induction t; simpl; intros; auto.
  - unfold extend.
    assert (h := H name).
    destruct (string_dec x); auto.
    rewrite e in h.
    rewrite eqb_refl in *.
    rewrite Bool.orb_true_l in *.
    firstorder; congruence.
  - erewrite IHt1; eauto; try erewrite IHt2; eauto; intros; assert (h := H _ H0);
      rewrite Bool.orb_false_iff in *; destruct h; now auto.
  - erewrite IHt1; eauto; try erewrite IHt2; eauto; intros; assert (h := H _ H0);
      rewrite Bool.orb_false_iff in *; destruct h; now auto.
Qed.

Lemma extend_subst : forall P pval vval x u n,
    no_capture_tm P u ->
    eval_tm vval u = n ->
    eval pval vval (subst_tm_pred P x u) <-> eval pval (extend vval x n) P.
Proof.
  induction P0; intros; simpl.
  - erewrite extend_subst_tm; now eauto.
  - destruct (string_dec x0 s); subst; simpl.
    + split; intros h n.
      -- eapply eval_ext; [| apply h].
         intros s'.
         unfold extend.
         destruct (string_dec s s'); eauto.
      -- eapply eval_ext; [| apply h].
         intros s'; unfold extend.
         destruct (string_dec s s'); eauto.
    + split; intros h n.
      -- (* First, swap the extends! *)
        assert (h_swap := extend_commut _ x0 s (eval_tm vval u) n vval n0).
        eapply eval_ext; [symmetry; apply h_swap|].
        eapply IHP0; eauto; [eapply no_capture_tm_forall; eauto|].
        erewrite <- no_capture_tm_forall_extend; now eauto.
      -- eapply IHP0; eauto; try eapply no_capture_tm_forall; eauto.
         erewrite <- no_capture_tm_forall_extend; eauto.
         assert (h_swap := extend_commut _ x0 s (eval_tm vval u) n vval n0).
         eapply eval_ext; [apply h_swap|].
         apply h; now auto.
  - split; intros Pr h; eapply IHP0; eauto.
  - rewrite IHP0_1; eauto;
    rewrite IHP0_2; eauto; now eauto.
Qed.


Lemma extend_subst' : forall P pval vval X Q,
    no_capture_prop P Q ->
    let V := fun n => eval pval (extend vval pattern_var n) Q in
    eval pval vval (subst_pred_pred P X Q) <-> eval (extend pval X V) vval P.
Proof.
  induction P0; intros; simpl.
  - unfold extend.
    destruct (string_dec X s); simpl; try reflexivity.
    subst.
    unfold V.
    rewrite extend_subst; [reflexivity | | reflexivity].
    unfold no_capture_prop in H.
    destruct H as [h1 [h2 [h3 h4]]].
    now auto.
  - split; intros h n; try apply IHP0.
    + pose (V' := (fun m => eval pval (extend (extend vval pattern_var m) s n) Q)).
      assert (forall n, V n <-> V' n).
      (* apply IHP0. *)
Admitted.

Print subst_pred_pred.

Lemma validates_extend_nfree : forall Γ pval vval x n,
    x # Γ ->
    validates pval vval Γ ->
    validates pval (extend vval x n) Γ.
Proof.
  induction Γ; simpl; intros pval vval s n nfree h; constructor.
  - rewrite Bool.orb_false_iff in nfree; destruct nfree as [free1 free2].
    inversion h; subst.
    apply nfree_tm_extend_pred; now auto.
  - inversion h; subst.
    apply IHΓ; auto.
    rewrite Bool.orb_false_iff in nfree; destruct nfree as [free1 free2].
    auto.
Qed.

Lemma validates_extend_nfree' : forall Γ pval vval X P,
    X ## Γ ->
    validates pval vval Γ ->
    validates (extend pval X P) vval Γ.
Proof.
  induction Γ; simpl; intros pval vval s n nfree h; constructor.
  - rewrite Bool.orb_false_iff in nfree; destruct nfree as [free1 free2].
    inversion h; subst.
    apply nfree_pred_extend_pred; auto.
  - inversion h; subst.
    apply IHΓ; auto.
    rewrite Bool.orb_false_iff in nfree; destruct nfree as [free1 free2].
    auto.
Qed.
  

Hint Resolve validates_extend_nfree validates_extend_nfree'.
    
Theorem soundness : forall Γ P, Γ ⊢ P -> Γ ⊧ P.
Proof.
  intros G P d; induction d.
  - intro; unfold validates; intros.
    rewrite Forall_forall in *.
    apply H0; now auto.
  - intro; simpl.
    intros.
    apply IHd.
    constructor; now auto.
  - unfold "⊧" in *; simpl in *.
    intros; apply IHd; now auto.
  - unfold "⊧" in *; simpl in *.
    intros; apply IHd; now auto.
  - unfold "⊧" in *; simpl in *.
    now auto.
  - unfold "⊧" in *; simpl in *.
    intros pval vval h.
    eapply extend_subst; now eauto.
  - unfold "⊧" in *; simpl in *.
    intros pval vval h;
    eapply extend_subst'; now eauto.
  - unfold "⊧" in *; simpl in *.
    unfold extend; simpl.
    intros; exfalso.
    assert (h := H0 (fun n => n <> 0)); simpl in h.
    destruct h; now auto.
  - unfold "⊧" in *; simpl in *.
    unfold extend; simpl; intros.
    assert (h := H0 (fun k => Pr (Nat.pred k))); simpl in h; now auto.
  - unfold "⊧" in *; simpl in *.
    unfold extend; simpl; intros.
    replace (n + 0) with n in H0 by auto; now auto.
  - unfold "⊧" in *; simpl in *.
    unfold extend; simpl; intros.
    replace (n + S n0) with (S (n + n0)) in H0 by auto; now auto.
  - unfold "⊧" in *; simpl in *.
    unfold extend; simpl; intros.
    replace (n * 0) with 0 in H0 by auto; now auto.
  - unfold "⊧" in *; simpl in *.
    unfold extend; simpl; intros.
    Require Import Lia.
    replace (n * S n0) with (n + n * n0) in H0 by lia; now auto.
  - unfold "⊧" in *; simpl in *.
    unfold extend; simpl; intros.
    induction n; now auto.
Qed.
