(* Let's build tools to reflect Coq proofs into HA2 *)

Require Import ha2.

Require Import Arith.

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

Coercion is_true : bool >-> Sortclass.


Fixpoint n_tm (n : nat) : tm :=
  match n with
  | 0 => Z
  | S n => Succ (n_tm n)
  end.

Lemma ren_closed : forall ξ t, closed_tm 0 t -> t⟨ξ⟩ = t.
Proof.
  induction t; simpl; asimpl; auto.
  - intro h; inversion h.
  - intros; f_equal; auto.
  - unfold is_true; rewrite Bool.andb_true_iff; intros (h1 & h2).
    rewrite IHt1, IHt2; auto.
  - unfold is_true; rewrite Bool.andb_true_iff; intros (h1 & h2).
    rewrite IHt1, IHt2; auto.
Qed.

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

Lemma closed_n_tm : forall n, closed_tm 0 (n_tm n).
Proof.
  induction n; simpl; auto.
Qed.

Hint Resolve closed_n_tm.

Lemma closed_add1 : forall n1 n2, closed_tm 0 (Add n1 n2) -> closed_tm 0 n1.
Proof.
  induction n1; simpl; auto.
  - intros ?; unfold is_true; repeat rewrite Bool.andb_true_iff; intuition.
  - intros ?; unfold is_true; repeat rewrite Bool.andb_true_iff; intuition.
Qed.


Lemma closed_add2 : forall n2 n1, closed_tm 0 (Add n1 n2) -> closed_tm 0 n2.
Proof.
  induction n2; simpl; auto.
  - intros ?; unfold is_true; repeat rewrite Bool.andb_true_iff; intuition.
  - intros ?; unfold is_true; repeat rewrite Bool.andb_true_iff; intuition.
  - intros ?; unfold is_true; repeat rewrite Bool.andb_true_iff; intuition.
Qed.

Hint Resolve closed_add2 closed_add1.

Lemma eq_add : forall Γ k l,
    Γ ⊢ Add (n_tm k) (n_tm l) ≃ n_tm (k + l).
Proof.
  intros Γ k l; revert k Γ; induction l; intros; simpl; rewrite Nat.add_comm; simpl.
  - replace (Add (n_tm k) Z ≃ n_tm k) with ((Add (var_tm 0) Z ≃ (var_tm 0))[(n_tm k) ..; ids]) by (asimpl; simpl; auto).
    apply forallt_elim.
    apply plus_Z.
  - apply trans_apply with (t2 := Succ (Add (n_tm k) (n_tm l))).
    + (* More replace hell... *)
      replace (Add (n_tm k) (Succ (n_tm l)) ≃ Succ (Add (n_tm k) (n_tm l)))
        with
        (Add (n_tm k) (Succ (var_tm 0)) ≃ Succ (Add (n_tm k) (var_tm 0)))[(n_tm l)..; ids] by (asimpl; repeat rewrite subst_closed; auto).
      apply forallt_elim.
      replace (all Add (n_tm k) (Succ (var_tm 0)) ≃ Succ (Add (n_tm k) (var_tm 0)))
        with
        (all Add (var_tm 1) (Succ (var_tm 0)) ≃ Succ (Add (var_tm 1) (var_tm 0)))[(n_tm k)..;ids] by
        (asimpl; repeat rewrite ren_closed; auto).
      apply forallt_elim.
      apply plus_S.
    + apply succ_apply.
      (* how did that happen? *)
      replace (l + k) with (k + l) by (apply Nat.add_comm).
      auto.
Qed.

Lemma tm_pattern_at_tm_mul_n : forall k t1 t2, tm_pattern_at_tm (Mult t1 t2) (n_tm k) = (n_tm k).
Proof.
  induction k; simpl; auto.
  intros; f_equal; auto.
Qed.

Lemma eq_mult : forall Γ k l,
    Γ ⊢ Mult (n_tm k) (n_tm l) ≃ n_tm (k * l).
Proof.
  intros Γ k l; revert k Γ; induction l; intros; simpl; rewrite Nat.mul_comm; simpl.
  - replace (Mult (n_tm k) Z ≃ Z) with
      (Mult (var_tm 0) Z ≃ Z)[(n_tm k)..; ids] by (asimpl; auto).
    apply forallt_elim.
    apply times_Z.
  - Print derives.
    apply trans_apply with (t2 := Add (n_tm k) (Mult (n_tm k) (n_tm l))).
    + Check times_S.
      replace
        (Mult (n_tm k) (Succ (n_tm l)) ≃ Add (n_tm k) (Mult (n_tm k) (n_tm l)))
        with
        (Mult (n_tm k) (Succ (var_tm 0)) ≃ Add (n_tm k) (Mult (n_tm k) (var_tm 0)))[(n_tm l)..; ids] by (asimpl; repeat rewrite subst_closed; auto).
      apply forallt_elim.
      replace (all Mult (n_tm k) (Succ (var_tm 0)) ≃ Add (n_tm k) (Mult (n_tm k) (var_tm 0))) with (all Mult (var_tm 1) (Succ (var_tm 0)) ≃ Add (var_tm 1) (Mult (var_tm 1) (var_tm 0)))[(n_tm k)..; ids] by (asimpl; repeat rewrite subst_closed, ren_closed; repeat rewrite ren_closed; auto).
      apply forallt_elim.
      apply times_S.
    + rewrite Nat.mul_comm.
      pattac (Mult (n_tm k) (n_tm l)).
      (* never do this! *)
      (* unfold tm_pattern_at_tm. *)
      rewrite tm_pattern_at_eq.
      rewrite tm_pattern_at_tm_mul_n.
      rewrite tm_pattern_at_tm_unfold.
      edestruct (eq_dec_neq (Mult (n_tm k) (n_tm l)) (Add (n_tm k) (Mult (n_tm k) (n_tm l)))); [congruence |].
      rewrite e; clear e.
      clear x.
      rewrite tm_pattern_at_tm_mul_n.
      rewrite tm_pattern_at_tm_unfold.
      rewrite eq_dec_eq.
      eapply eq_subst.
      -- apply sym_apply.
         apply IHl.
      -- asimpl.
         repeat rewrite subst_closed; auto.
         apply eq_add.
Qed.
      

Lemma eq_norm : forall Γ vval t,
    closed_tm 0 t ->
    Γ ⊢ t ≃ n_tm (eval_tm vval t).
Proof.
  intros Γ vval t; induction t; intros; simpl; auto.
  - inversion H.
  - apply eq_refl.
  - inversion H.
    assert (h := IHt H1).
    apply succ_apply; auto.
  - apply trans_apply with (t2 := Add (n_tm (eval_tm vval t1)) (n_tm (eval_tm vval t2))); [ | apply eq_add].
    replace (Add t1 t2 ≃ Add (n_tm (eval_tm vval t1)) (n_tm (eval_tm vval t2))) with
      (Add t1 t2 ≃ Add (var_tm 0) (n_tm (eval_tm vval t2)))[(n_tm (eval_tm vval t1))..; ids] by (asimpl; repeat rewrite subst_closed; eauto).
    eapply eq_subst; eauto; asimpl; repeat rewrite subst_closed; eauto.
    replace (Add t1 t2 ≃ Add t1 (n_tm (eval_tm vval t2))) with
      (Add t1 t2 ≃ Add t1 (var_tm 0))[(n_tm (eval_tm vval t2))..; ids] by (asimpl; repeat rewrite subst_closed; eauto).
    eapply eq_subst; eauto; asimpl; repeat rewrite subst_closed; eauto.
    apply eq_refl.
  - apply trans_apply with (t2 := Mult (n_tm (eval_tm vval t1)) (n_tm (eval_tm vval t2))); [ | apply eq_mult].
    replace (Mult t1 t2 ≃ Mult (n_tm (eval_tm vval t1)) (n_tm (eval_tm vval t2))) with
      (Mult t1 t2 ≃ Mult (var_tm 0) (n_tm (eval_tm vval t2)))[(n_tm (eval_tm vval t1))..; ids] by (asimpl; repeat rewrite subst_closed; eauto).
    eapply eq_subst; eauto; asimpl; repeat rewrite subst_closed; eauto.
    replace (Mult t1 t2 ≃ Mult t1 (n_tm (eval_tm vval t2))) with
      (Mult t1 t2 ≃ Mult t1 (var_tm 0))[(n_tm (eval_tm vval t2))..; ids] by (asimpl; repeat rewrite subst_closed; eauto).
    eapply eq_subst; eauto; asimpl; repeat rewrite subst_closed; eauto.
    apply eq_refl.
Qed.

Theorem eq_complete : forall Γ t u,
    closed_tm 0 t ->
    closed_tm 0 u ->
    [] ⊧ t ≃ u ->
    Γ ⊢ t ≃ u.
Proof.
  unfold "⊧".
  simpl.
  intros.
  assert (eval_tm id t = eval_tm id u).
  - intros.
    pattern (eval_tm id u) at 1.
    eapply H1; eauto.
    unfold validates; auto.
  - apply trans_apply with (t2 := n_tm (eval_tm id u)).
    + rewrite <- H2.
      apply eq_norm; auto.
    + apply sym_apply.
      apply eq_norm; auto.
      Unshelve.
      unfold PVal.
      apply (fun _ _ => False).
Qed.

Require Import Lia.

Lemma lower_closed : forall t level, closed_tm 0 t -> lower_tm level t = Some t.
Proof.
  induction t; simpl; intros; try congruence.
  - destruct (Nat.ltb_spec n 0); try lia; congruence.
  - rewrite IHt; simpl; auto.
  - unfold is_true in *.
    rewrite Bool.andb_true_iff in H.
    rewrite IHt1, IHt2; simpl; intuition.
  - unfold is_true in *.
    rewrite Bool.andb_true_iff in H.
    rewrite IHt1, IHt2; simpl; intuition.
Qed.

Lemma match_closed : forall level t, closed_tm 0 t -> match_var level level t = Success t.
  unfold match_var.
  intros.
  destruct (Nat.ltb_spec level level); try lia.
  destruct (Nat.eqb_spec level level); try lia.
  rewrite lower_closed; auto.
Qed.

Lemma match_closed' : forall level n t, closed_tm 0 t -> level <> n -> match_var level n t = Fail.
  unfold match_var.
  intros.
  destruct (Nat.ltb_spec n level).
  - destruct t; simpl in *; auto.
    unfold is_true in *; rewrite Nat.ltb_lt in H; lia.
  - destruct (Nat.eqb_spec n level); try lia.
    destruct t; try congruence.
    simpl in H.
    unfold is_true in *; rewrite Nat.ltb_lt in H; lia.
Qed.

Lemma match_closed_tm : forall t level, closed_tm 0 t -> match_tm level t t = Empty.
Proof.
  induction t; simpl; auto.
  - intros ?; destruct (Nat.ltb_spec n 0); [lia | congruence].
  - intros level; unfold is_true; rewrite Bool.andb_true_iff; intros (h1 & h2);
      rewrite IHt1, IHt2; intuition.
  - intros level; unfold is_true; rewrite Bool.andb_true_iff; intros (h1 & h2);
      rewrite IHt1, IHt2; intuition.
Qed.
    

Require Import Coq.Classes.EquivDec.


Lemma neq_closed : forall n m Γ, n <> m -> Γ ⊢ n_tm n ≄ n_tm m.
Proof.
  induction n; induction m; simpl; intros; try congruence.
  - apply imp_intro.
    apply imp_elim with (P := (Succ (n_tm m) ≃ Z)).
    + eapply apply_forallt; [| apply zero_S; eauto].
      simpl; rewrite match_closed; auto.
      reflexivity.
    + apply sym_apply.
      apply (axiom 0); auto.
  - eapply apply_forallt; [ | apply zero_S; eauto].
    simpl; rewrite match_closed; auto; reflexivity.
  - apply imp_intro.
    apply imp_elim with (P := (n_tm n) ≃ (n_tm m)).
    + apply IHn; auto.
    + eapply imp_elim; [| apply (axiom 0); simpl; eauto].
      eapply apply_forallt2 with (t1 := (n_tm n)); [ | | apply inj_S].
      -- simpl; rewrite match_closed; [ | asimpl; rewrite ren_closed; auto].
         asimpl.
         unfold match_var; simpl.
         rewrite ren_closed; auto.
         unfold join.
         rewrite eq_dec_eq.
         auto.
      -- simpl; rewrite match_closed; auto.
         rewrite ren_closed; auto.
         asimpl.
         rewrite match_closed_tm; auto.
         unfold join.
         rewrite eq_dec_eq; eauto.
Qed.


(* Ooof this is not trivial from the other one *)
Theorem neq_complete : forall Γ t u,
    closed_tm 0 t ->
    closed_tm 0 u ->
    [] ⊧ t ≄ u ->
    Γ ⊢ t ≄ u.
Proof.
  intros Γ t u cl_t cl_u neq_sem.
  apply imp_intro.
  apply imp_elim with (P := (n_tm (eval_tm id t)) ≃ (n_tm (eval_tm id u))).
  - assert (eval_tm id t <> eval_tm id u).    
    + unfold "⊧" in *.
      simpl in neq_sem.
      intro.
      eapply neq_sem; unfold validates; auto.
      -- rewrite H; auto.
      -- exact 0.
    + apply neq_closed; auto.
  - apply trans_apply with (t2 := t) ; [apply sym_apply; apply eq_norm; auto|].
    apply trans_apply with (t2 := u); [| apply eq_norm; auto].
    apply (axiom 0); auto.
    Unshelve.
    unfold PVal.
    apply (fun _ _ => False).
Qed.

Lemma subst_lift_tm : forall (t : tm) ξ, t[ξ >> var_tm] = t⟨ξ⟩.
Proof.
  induction t; intros; asimpl; try rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

Lemma subst_lift : forall (P : prop) (ξ : fin -> fin) (σ : fin -> tm), P[ξ >> σ; var_pred] = (P ⟨ξ; id⟩ [σ; ids]).
Proof.
  intros.
  asimpl.
  auto.
Qed.

Lemma subst_lift' : forall (P : prop) ξ, P[ξ >> var_tm; var_pred] = P ⟨ξ; id⟩.
Proof.
  intros.
  replace (P ⟨ξ; id⟩) with (P ⟨ξ; id⟩[var_tm; ids]) by (asimpl; auto).
  apply subst_lift.
Qed.

Lemma exfalso_apply : forall Γ P, Γ ⊢ ⊥ -> Γ ⊢ P.
Proof.
  intros Γ P fls.
  replace P with (P⟨↑; ids⟩ [(var_tm 0)..; ids]) by (asimpl; unfold idsRen; asimpl; auto).
  apply compr_elim.
  replace (var_tm 0 ∈ {{_ | P ⟨↑; ids⟩ }}) with
    (var_tm 0 ∈ {{_ | P ⟨↑ >> ↑; ids⟩ }})[(var_tm 0)..; ids]
    by (asimpl;
       unfold idsRen;
       asimpl;
        rewrite subst_lift'; auto).
  apply forallt_elim.  
  replace (all var_tm 0 ∈ {{_ | P ⟨↑ >> ↑ ; ids⟩ }}) with
    (all var_tm 0 ∈ var_pred 0)[ids; {{_ | P ⟨↑ ; ids⟩ }}..] by (asimpl; auto).
  apply forallP_elim; auto.
Qed.

Definition and_prop P Q := FORALL (P⟨id; ↑⟩ ⇒ Q⟨id; ↑⟩ ⇒ all (var_tm 0) ∈ (var_pred 0)) ⇒ all (var_tm 0) ∈ (var_pred 0).

Notation "P ∧ Q" := (and_prop P Q) (at level 25).

Definition or_prop P Q := FORALL (P⟨id; ↑⟩ ⇒ all (var_tm 0) ∈ (var_pred 0)) ⇒
                            (Q⟨id; ↑⟩ ⇒ all (var_tm 0) ∈ (var_pred 0)) ⇒
                            all (var_tm 0) ∈ (var_pred 0).

Notation "P ∨ Q" := (or_prop P Q) (at level 25).


Class complete Γ P := { reflect : Γ ⊧ P -> Γ ⊢ P }.

Lemma superweak : forall Γ P, nil ⊢ P -> Γ ⊢ P.
Proof.
  induction Γ; auto.
  intros.
  apply weakening; auto.
Qed.

Lemma reflect_closed {P : prop} [cp : complete nil P] : forall Γ, [] ⊧ P -> Γ ⊢ P.
  intros; apply superweak.
  apply reflect; auto.
Qed.

Instance complete_eq (t u : tm) : closed_tm 0 t -> closed_tm 0 u -> complete nil (t ≃ u).
intros; constructor; intros; apply eq_complete; auto.
Qed.

Instance complete_neq (t u : tm) : closed_tm 0 t -> closed_tm 0 u -> complete nil (t ≄ u).
intros; constructor; intros; apply neq_complete; auto.
Qed.

(* Useless on its own, but may find use later. *)
Instance complete_false : complete nil ⊥.
constructor; unfold "⊧"; simpl; intros.
exfalso.
apply (H (fun _ _ => False) (fun _ => 0)); unfold validates; auto.
exact 0.
Qed.

(* This does *not* hold with the current definition of completeness *)
Instance complete_imp {Γ P Q} {cq : complete (P::Γ) Q} : complete Γ (P ⇒ Q).
constructor; intros.
apply imp_intro.
apply reflect.
unfold "⊧" in *; simpl in *; intros.
apply H.
- inversion H0; subst; auto.
- inversion H0; auto.
Qed.

Print "⊧".

Definition bot_pval : PVal := fun _ _ => False.
Definition bot_vval : VVal := fun _ => 0.

Lemma val_nil : validates bot_pval bot_vval nil.
Proof.
  unfold validates; auto.
Qed.

Theorem ex_refl :
  forall P, [] ⊢ ∃ P -> exists n, eval_prop bot_pval (n, bot_vval) P.
Proof.
  intros.
  assert (h : [] ⊧ ∃ P) by (apply soundness; auto).
  unfold "⊧" in *; simpl in *.
  apply (h bot_pval bot_vval val_nil (fun _ => exists n, eval_prop bot_pval (n, bot_vval) P)); [ | exact 0].
  intros.
  exists n.
  rewrite eval_ren in H0; asimpl in *.
  auto.
Qed.

(* Todo: prove that there actually is a *provable* inhabitant! (at least when we're Deta_0) *)
                   
Theorem and_intro : forall Γ P Q, Γ ⊢ P ⇒ Q ⇒ P ∧ Q.
  intros.
  repeat apply imp_intro.
  apply forallP_intro.
  repeat apply imp_intro.
  eapply imp_elim with (P := Q ⟨id;↑⟩).
  - eapply imp_elim with (P := P ⟨id;↑⟩); [apply (axiom 0); auto |].
    apply (axiom 2); auto.
  - apply (axiom 1); auto.
Qed.

Lemma sheesh : forall (P : prop) ξ, P [ξ >> var_tm; var_pred] = P ⟨ξ; id⟩.
Proof.
  induction P using prop_pred_ind with (P0 :=  fun P => forall ξ, P [ξ >> var_tm; var_pred] = P ⟨ξ; id⟩); simpl; asimpl; try rewrite IHP; auto.
  - intros; rewrite subst_ren; rewrite IHP; asimpl; auto.
  - intros.
    rewrite ext_prop with (tautm := (0, ξ >> S) >> var_tm)(taupred := var_pred).
    + rewrite IHP; auto.
    + destruct x; asimpl; auto.
    + auto.
  - intros; rewrite ext_prop with (tautm := ξ >> var_tm)(taupred := var_pred); auto.
    rewrite IHP.
    rewrite extRen_prop with (zetatm := ξ)(zetapred := (0, S)); auto.
    destruct x; auto.
  - intros; rewrite IHP1, IHP2; auto.
  - intros.
    rewrite ext_prop with (tautm := (0, ξ >> S) >> var_tm)(taupred := var_pred); auto.
    + rewrite IHP; auto.
    + destruct x; asimpl; auto.
Qed.

Theorem and_elim1 : forall Γ P Q, Γ ⊢ P ∧ Q ⇒ P.
Proof.                     
  intros; repeat apply imp_intro.
  unfold "∧".
  replace P with P⟨↑; id⟩[(var_tm 0)..; ids] at 2 by (asimpl; auto).
  apply compr_elim.
  pattac (var_tm 0).
  apply forallt_elim.
  simpl; asimpl.
  apply imp_elim with (P := P ⇒ Q ⇒ (all var_tm 0 ∈ {{ _ | P⟨↑ >> S ; id⟩}})).
  - pose (Pu := P ⟨↑ >> S; id⟩).
    replace (P ⟨↑ >> S; id⟩) with Pu by reflexivity.
    replace (ren_prop (↑ >> S) id P) with Pu by reflexivity.
    replace ((P ⇒ Q ⇒ (all var_tm 0 ∈ ({{ _ | Pu }}))) ⇒ (all var_tm 0 ∈ ({{ _ | Pu }})))
      with
      ((P⟨id;↑⟩ ⇒ Q ⟨id;↑⟩ ⇒ (all var_tm 0 ∈ var_pred 0)) ⇒ (all var_tm 0 ∈ var_pred 0))[ids; {{ _ | P⟨↑;id⟩ }}..] by (subst Pu; asimpl; auto).
    apply forallP_elim.
    apply (axiom 0); auto.
  - repeat apply imp_intro.
    apply forallt_intro.
    apply compr_intro.
    apply (axiom 1); asimpl; simpl.
    replace (P ⟨↑; id⟩) with (subst_prop (↑ >> var_tm) var_pred P); auto.
    
    replace (subst_prop (↑ >> var_tm) var_pred P) with (P ⟨↑; id⟩[var_tm; var_pred]) ; (asimpl; auto).
    rewrite sheesh; auto.
Qed.

Theorem and_elim2 : forall Γ P Q, Γ ⊢ P ∧ Q ⇒ Q.
Proof.                     
  intros; repeat apply imp_intro.
  unfold "∧".
  replace Q with Q⟨↑; id⟩[(var_tm 0)..; ids] at 2 by (asimpl; auto).
  apply compr_elim.
  pattac (var_tm 0).
  apply forallt_elim.
  simpl; asimpl.
  apply imp_elim with (P := P ⇒ Q ⇒ (all var_tm 0 ∈ {{ _ | Q⟨↑ >> S ; id⟩}})).
  - pose (Qu := Q ⟨↑ >> S; id⟩).
    replace (Q ⟨↑ >> S; id⟩) with Qu by reflexivity.
    replace (ren_prop (↑ >> S) id Q) with Qu by reflexivity.
    replace ((P ⇒ Q ⇒ (all var_tm 0 ∈ ({{ _ | Qu }}))) ⇒ (all var_tm 0 ∈ ({{ _ | Qu }})))
      with
      ((P⟨id;↑⟩ ⇒ Q ⟨id;↑⟩ ⇒ (all var_tm 0 ∈ var_pred 0)) ⇒ (all var_tm 0 ∈ var_pred 0))[ids; {{ _ | Q⟨↑;id⟩ }}..] by (subst Qu; asimpl; auto).
    apply forallP_elim.
    apply (axiom 0); auto.
  - repeat apply imp_intro.
    apply forallt_intro.
    apply compr_intro.
    apply (axiom 0); asimpl; simpl.
    replace (Q ⟨↑; id⟩) with (subst_prop (↑ >> var_tm) var_pred Q); auto.
    
    replace (subst_prop (↑ >> var_tm) var_pred Q) with (Q ⟨↑; id⟩[var_tm; var_pred]) ; (asimpl; auto).
    rewrite sheesh; auto.
Qed.

Theorem or_intro1 : forall Γ P Q, Γ ⊢ P ⇒ P ∨ Q.
Proof.
  intros; repeat apply imp_intro.
  unfold "∨".
  apply forallP_intro.
  repeat apply imp_intro.
  eapply imp_elim; [apply (axiom 1); simpl; eauto | ].
  apply (axiom 2); simpl; auto.
Qed.

Theorem or_intro2 : forall Γ P Q, Γ ⊢ Q ⇒ P ∨ Q.
Proof.
  intros; repeat apply imp_intro.
  unfold "∨".
  apply forallP_intro.
  repeat apply imp_intro.
  eapply imp_elim; [apply (axiom 0); simpl; eauto | ].
  apply (axiom 2); simpl; auto.
Qed.


Theorem or_elim : forall Γ P Q R, Γ ⊢ P ⇒ R -> Γ ⊢ Q ⇒ R -> Γ ⊢ P ∨ Q ⇒ R.
Proof.
  intros; repeat apply imp_intro.
  unfold "∨".
  replace R with (R⟨↑; id⟩[(var_tm 0)..; ids]) by (asimpl; auto).
  apply compr_elim.
  pattac (var_tm 0).  
  apply forallt_elim.
  simpl; asimpl.
  pose (R' := {{_ | ren_prop (↑ >> S) id R}}).
  replace ({{_ | ren_prop (↑ >> S) id R}}) with R' by auto.
  apply imp_elim with (P := Q ⇒ (all var_tm 0 ∈ R')).
  - apply imp_elim with (P := P ⇒ (all var_tm 0 ∈ R')).
    + replace ((P ⇒ (all var_tm 0 ∈ R')) ⇒ (Q ⇒ (all var_tm 0 ∈ R')) ⇒ (all var_tm 0 ∈ R'))
        with ((P⟨id; ↑⟩ ⇒ (all var_tm 0 ∈ var_pred 0)) ⇒ (Q⟨id; ↑⟩ ⇒ (all var_tm 0 ∈ var_pred 0)) ⇒ (all var_tm 0 ∈ var_pred 0))[ids; {{ _ | R⟨↑; id⟩}}..] by (asimpl; auto).
      apply forallP_elim; apply (axiom 0); auto.
    + apply imp_intro, forallt_intro, compr_intro.
      asimpl.
      rewrite sheesh.
      eapply imp_elim; [ | apply (axiom 0); simpl; auto].
      unfold lift_tm; simpl.
      apply weakening.
      apply weakening.
      replace (P ⟨↑;id⟩ ⇒ R ⟨↑;id⟩) with (P ⇒ R)⟨↑; id⟩ by (asimpl; auto).
      apply lift_derives; auto.
  -  apply imp_intro, forallt_intro, compr_intro.
      asimpl.
      rewrite sheesh.
      eapply imp_elim; [ | apply (axiom 0); simpl; auto].
      unfold lift_tm; simpl.
      apply weakening.
      apply weakening.
      replace (Q ⟨↑;id⟩ ⇒ R ⟨↑;id⟩) with (Q ⇒ R)⟨↑; id⟩ by (asimpl; auto).
      apply lift_derives; auto.
Qed.

(* TODO: completeness for ∨ and ∧ *)
Instance and_complete {P Q}{cpltP : complete nil P}{cpltQ : complete nil Q} : complete nil (P ∧ Q).
Proof.
  constructor.
  destruct cpltP, cpltQ.
  intros.
  eapply imp_elim; [| apply reflect1].
  eapply imp_elim; [| apply reflect0].
  - apply and_intro.
  - unfold "∧" in H.
    unfold models in H.
    simpl in H.
    intro; intros.
    apply (H pval vval); eauto; [| exact 0].
    rewrite eval_ren; asimpl.
    auto.
  - unfold "∧" in H.
    unfold models in H.
    simpl in H.
    intro; intros.
    apply (H pval vval); eauto; [| exact 0].
    intros _; rewrite eval_ren; asimpl.
    auto.
Qed.

Lemma closed_eval_tm : forall t vval vval',
 closed_tm 0 t -> eval_tm vval t = eval_tm vval' t.
Proof.
  induction t; simpl; intros; unfold is_true in *; auto.
  - rewrite Nat.ltb_lt in *; lia.
  - rewrite Bool.andb_true_iff in *; intuition.
  - rewrite Bool.andb_true_iff in *; intuition.
Qed.


Lemma closed_eval : forall P vval pval vval' pval',
 closed_prop 0 0 P -> eval_prop pval vval P <-> eval_prop pval' vval' P.
Proof.
  induction P using prop_pred_ind
    with (P0 := fun p => forall vval pval vval' pval', closed_pred 0 0 p -> forall n, eval_pred pval vval p n <-> eval_pred pval' vval' p n); simpl; unfold is_true; intros; auto.
  - rewrite Bool.andb_true_iff in *; erewrite closed_eval_tm; try apply IHP; intuition.
  - admit.
  - admit.
  - rewrite Bool.andb_true_iff in *.
    rewrite IHP1, IHP2; [reflexivity | |]; intuition.
  - rewrite Nat.ltb_lt in *; lia.
  - admit.
Admitted.

(* is this even true? Certainly if P and Q are closed... *)
Instance or_complete {P Q}{cpltP : complete nil P}{cpltQ : complete nil Q} : closed_prop 0 0 P -> closed_prop 0 0 Q -> complete nil (P ∨ Q).
Proof.
  intros clp clq; constructor; destruct cpltP, cpltQ; unfold models; simpl; intros h.
  (* Unclear that this holds! what if P is is_even n and Q is is_odd n? *)
  assert (h := h bot_pval bot_vval val_nil (fun _ => eval_prop bot_pval bot_vval P \/ eval_prop bot_pval bot_vval Q)).
  edestruct h.
  - rewrite eval_ren; asimpl; intros; left; auto.
  - rewrite eval_ren; asimpl; intros; right; auto.
  - exact 0.
  - eapply imp_elim; [ apply or_intro1 |].
    apply reflect0; intro; intros.
    erewrite closed_eval; eauto.
  - eapply imp_elim; [apply or_intro2 |].
    apply reflect1; intro; intros.
    erewrite closed_eval; eauto.
Qed.

(* TODO: complete nil P[#n..; ids] -> complete nil ∃ P *)
