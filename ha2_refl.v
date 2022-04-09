(* Let's build tools to reflect Coq proofs into HA2 *)

Require Import ha2.

Locate "≃".

Require Import Arith.

Search Nat.ltb.

Fixpoint closed_tm (level : fin) (t : tm) : bool :=
  match t with
  | var_tm n => n <? level
  | Succ t => closed_tm level t
  | Z => true
  | Add t1 t2
  | Mult t1 t2 => closed_tm level t1 && closed_tm level t2
  end.


Fixpoint closed_prop (t_level p_level : fin) (P : prop) : bool :=
  match P with
  | n ∈ P => closed_tm t_level n && closed_pred t_level p_level P
  | all P => closed_prop (shift t_level) p_level P
  | FORALL P => closed_prop t_level (shift p_level) P
  | P ⇒ Q => closed_prop t_level p_level P && closed_prop t_level p_level Q
  end
with
    closed_pred (t_level p_level : fin) (P : pred) : bool :=
      match P with
      | var_pred n => n <? p_level
      | {{ _ | P }} => closed_prop (shift t_level) p_level P
      end.

Notation "t ≄ u" := ((t ≃ u) ⇒ ⊥)(at level 20).
Locate "∃".

Import ListNotations.

Check is_true.

Coercion is_true : bool >-> Sortclass.


Fixpoint n_tm (n : nat) : tm :=
  match n with
  | 0 => Z
  | S n => Succ (n_tm n)
  end.


Lemma subst_closed : forall σ t, closed_tm 0 t -> t[σ] = t.
Proof.
  induction t; simpl; asimpl; auto.
  - intro h; inversion h.
  - intros; rewrite IHt; auto.
  - unfold is_true.
    rewrite Bool.andb_true_iff.
    intros (h1 & h2).
    rewrite IHt1, IHt2; auto.
  - unfold is_true.
    rewrite Bool.andb_true_iff.
    intros (h1 & h2).
    rewrite IHt1, IHt2; auto.
Qed.


Lemma tm_pattern_at_impl : forall P Q u, tm_pattern_at u (P ⇒ Q) = (tm_pattern_at u P) ⇒ (tm_pattern_at u Q).
Proof.
  intros; reflexivity.
Qed.

Lemma tm_pattern_at_eq : forall t1 t2 u, tm_pattern_at u (t1 ≃ t2) = (tm_pattern_at_tm u t1) ≃ (tm_pattern_at_tm u t2).
Proof.
  intros; reflexivity.
Qed.

Ltac patme u := (rewrite (tm_pattern_at_subst u); repeat rewrite tm_pattern_at_impl, tm_pattern_at_eq).


Lemma trans_apply : forall Γ t1 t2 t3,
    Γ ⊢ t1 ≃ t2 -> Γ ⊢ t2 ≃ t3 -> Γ ⊢ t1 ≃ t3.
Proof.
  intros.
  destruct (eq_dec_tm t1 t3); [subst; apply eq_refl|].
  destruct (eq_dec_tm t2 t3); [subst; now auto|].
  destruct (eq_dec_tm t1 t2); [subst; now auto|].
  apply imp_elim with (P := t2 ≃ t3); auto.
  apply imp_elim with (P := t1 ≃ t2); auto.
  patme t3; apply forallt_elim.
  patme t2; apply forallt_elim.
  patme t1; apply forallt_elim.

Lemma eq_add : forall Γ k l,
    Γ ⊢ Add (n_tm k) (n_tm l) ≃ n_tm (k + l).
Proof.
  Search (_ + _).
  intros Γ k l; revert k Γ; induction l; intros; simpl; rewrite Nat.add_comm; simpl.
  - replace (Add (n_tm k) Z ≃ n_tm k) with ((Add (var_tm 0) Z ≃ (var_tm 0))[(n_tm k) ..; ids]) by (asimpl; simpl; auto).
    apply forallt_elim.
    apply plus_Z.
  - apply imp_elim with (P := Succ (Add (n_tm k) (n_tm l)) ≃ Succ (n_tm (l+k))).
    + apply imp_elim with (P := Add (n_tm k) (Succ (n_tm l)) ≃ Succ (Add (n_tm k) (n_tm l))).
      -- Check eq_trans.
         patme (Succ (n_tm (l+k))).
         apply forallt_elim.
         patme 
         
         pose (goal := Add (n_tm k) (Succ (n_tm l)) ≃ Succ (Add (n_tm k) (n_tm l))
                           ⇒ Succ (Add (n_tm k) (n_tm l)) ≃ Succ (n_tm (l + k))
                           ⇒ Add (n_tm k) (Succ (n_tm l)) ≃ Succ (n_tm (l + k))).
         replace (Add (n_tm k) (Succ (n_tm l)) ≃ Succ (Add (n_tm k) (n_tm l))
                      ⇒ Succ (Add (n_tm k) (n_tm l)) ≃ Succ (n_tm (l + k))
                      ⇒ Add (n_tm k) (Succ (n_tm l)) ≃ Succ (n_tm (l + k))) with goal by reflexivity.
         

Lemma eq_norm : forall Γ vval t,
    closed_tm 0 t ->
    Γ ⊢ t ≃ n_tm (eval_tm vval t).
Proof.
  intros Γ vval t; induction t; intros; simpl; auto.
  - inversion H.
  - apply eq_refl.
  - inversion H.
    assert (h := IHt H1).
    Locate "≃".
    replace (Succ t ≃ Succ (n_tm (eval_tm vval t)))
      with ((Succ t ≃ Succ (var_tm 0))[(n_tm (eval_tm vval t))..; ids]) by (asimpl; rewrite subst_closed; auto).
    apply compr_elim.
    eapply imp_elim with (P := t ∈ {{_ | Succ t ≃ Succ (var_tm 0) }}).
    + replace (t ∈ ({{ _ | Succ t ≃ Succ (var_tm 0)}})
                 ⇒ n_tm (eval_tm vval t) ∈ ({{ _ | Succ t ≃ Succ (var_tm 0)}})) with
        ((t ∈ var_pred 0 ⇒ n_tm (eval_tm vval t) ∈ var_pred 0)[ids; {{ _ | Succ t ≃ Succ (var_tm 0)}}..]) by (asimpl; auto).
      apply forallP_elim; auto.
    + apply compr_intro.
      asimpl; rewrite subst_closed; auto.
      apply eq_refl.
  - 
Qed.

Theorem eq_complete : forall t u,
    closed_tm 0 t ->
    closed_tm 0 u ->
    [] ⊧ t ≃ u ->
    [] ⊢ t ≃ u.
Proof.
  unfold "⊧".
  simpl.

