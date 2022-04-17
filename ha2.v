(* A relatively straightforward formalization of HA^2 *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Export ha2_syn.

Notation "P ⇒ Q" := (Imp P Q)(at level 30, right associativity).

Notation "t ∈ P" := (Mem t P)(at level 20, no associativity).

Notation "'FORALL' P" := (ForallP P)(at level 33).
Notation "'all'  P" := (Forallt P) (at level 33).

Notation "{{ '_' | P }}" := (Compr P)(at level 33).

Check (all var_tm 0 ∈ var_pred 0 ⇒ var_tm 0 ∈ var_pred 0).
Check (var_tm 0 ∈ {{ _ | var_tm 0 ∈ var_pred 0 }}).

Definition PVal := fin -> fin -> Prop.

Definition VVal := fin -> nat.

Fixpoint eval_tm (vval : VVal) (t : tm) : nat :=
  match t with
  | var_tm x => vval x
  | Succ t => S (eval_tm vval t)
  | Z => 0
  | Add t1 t2 => (eval_tm vval t1) + (eval_tm vval t2)
  | Mult t1 t2 => (eval_tm vval t1) * (eval_tm vval t2)
  end.

Definition default_pred := fun _ : nat => False.
Definition default_prop := False.

Fixpoint eval_pred (pval : PVal) (vval : VVal) (P : pred) : nat -> Prop :=
  match P with
  | var_pred X => pval X
  | {{ _ | P }} => fun n => eval_prop pval (n, vval) P
  end
with eval_prop (pval : PVal) (vval : VVal) (P : prop) : Prop :=
  match P with
  | t ∈ P => (eval_pred pval vval P) (eval_tm vval t)
  | all P => forall n, eval_prop pval (n, vval) P
  | FORALL P => forall (Pr : nat -> Prop), eval_prop (Pr, pval) vval P
  | P ⇒ Q => (eval_prop pval vval P) -> (eval_prop pval vval Q)
  end.

Import ListNotations.

Definition ctxt := list prop.

Notation "t1 ≃ t2" := (FORALL t1 ∈ var_pred 0 ⇒ t2 ∈ var_pred 0) (at level 20).

(* notionally: ∃ x, Q(x) := ∀ P, (∀ x, Q(x) ⇒ P) ⇒ P *)
Notation "∃ Q" := (FORALL (all Q⟨id; ↑⟩ ⇒ all var_tm 0 ∈ var_pred 0) ⇒ all var_tm 0 ∈ var_pred 0)(at level 10).

Notation "⊥" := (FORALL all var_tm 0 ∈ var_pred 0).

Definition lift_prop (Γ : ctxt) : ctxt :=
  List.map (fun P => P⟨id;↑⟩) Γ.

Definition lift_tm (Γ : ctxt) : ctxt :=
  List.map (fun P => P⟨↑; id⟩) Γ.


Inductive derives : ctxt -> prop -> Type :=
| axiom : forall n Γ P, List.nth_error Γ n = Init.Datatypes.Some P -> derives Γ P
| imp_intro : forall Γ P Q,
    derives (P::Γ) Q -> derives Γ (P ⇒ Q)
| forallt_intro : forall Γ P, derives (lift_tm Γ) P -> derives Γ (all P)
| forallP_intro : forall Γ P,  derives (lift_prop Γ) P -> derives Γ (FORALL P)
| imp_elim : forall Γ P Q, derives Γ (P ⇒ Q) -> derives Γ P -> derives Γ Q
| forallt_elim : forall Γ (P : prop) (t : tm),
    derives Γ (all P) -> derives Γ P[t..;ids]
| forallP_elim : forall Γ P (Q : pred),
    derives Γ (FORALL P) -> derives Γ P[ids; Q..]
| compr_intro : forall Γ P (t : tm),
    derives Γ P[t..;ids] ->
    derives Γ (t ∈ {{ _ | P }})
| compr_elim : forall Γ P (t : tm),
    derives Γ (t ∈ {{ _ | P }}) ->
    derives Γ P[t..;ids]
| zero_S : forall Γ, derives Γ (all Succ (var_tm 0) ≃ Z ⇒ ⊥)
| inj_S : forall Γ,
    derives Γ (all all (Succ (var_tm 1)) ≃ (Succ (var_tm 0)) ⇒ (var_tm 1 ≃ var_tm 0))
| plus_Z : forall Γ, derives Γ (all Add (var_tm 0) Z ≃ var_tm 0)
| plus_S : forall Γ, derives Γ (all all Add (var_tm 1) (Succ (var_tm 0)) ≃ Succ (Add (var_tm 1) (var_tm 0)))
| times_Z : forall Γ, derives Γ (all Mult (var_tm 0) Z ≃ Z)
| times_S : forall Γ,
    derives Γ (all all Mult (var_tm 1) (Succ (var_tm 0)) ≃ (Add (var_tm 1) (Mult (var_tm 1) (var_tm 0))))
(* We don't *need* this: we can just define a predicate Nat(n), List(n) etc. *)
(* | ind : forall Γ, *)
(*     derives Γ (FORALL Z ∈ var_pred 0 ⇒ (all var_tm 0 ∈ var_pred 0 ⇒ (Succ (var_tm 0)) ∈ var_pred 0) ⇒ all var_tm 0 ∈ var_pred 0) *)
.


Notation "Γ ⊢ P" := (derives Γ P)(at level 40).

Definition validates(pval : PVal)(vval : VVal) (Γ : ctxt) : Prop :=
  Forall (eval_prop pval vval) Γ.

Definition models (Γ : ctxt)(P : prop) : Prop :=
  forall pval vval,
    validates pval vval Γ -> eval_prop pval vval P.

Notation "Γ ⊧ P" := (models Γ P)(at level 40).

Lemma forall_iff : forall A (P Q : A -> Prop),
    (forall x, P x <-> Q x) ->
    (forall x, P x) <-> (forall x, Q x).
Proof.
  firstorder.
Qed.

Lemma impl_iff : forall (P Q R S : Prop),
    (P <-> R) -> (Q <-> S) -> (P -> Q) <-> (R -> S).
Proof.
  intuition.
Qed.

Lemma eval_tm_ext : forall t vval vval',
    (forall x, vval x = vval' x) ->
    eval_tm vval t = eval_tm vval' t.
Proof.
  induction t; intros; simpl; auto.
Qed.

Scheme prop_pred_ind := Induction for prop Sort Prop
    with pred_prop_ind := Induction for pred Sort Prop.

Check prop_pred_ind.

    
Lemma eval_ext : forall P pval vval vval',
    (forall x, vval x = vval' x) ->
    eval_prop pval vval P <-> eval_prop pval vval' P.
Proof.
  intros P.
  induction P using prop_pred_ind with
    (P0 := fun p => forall pval vval vval',
               (forall x, vval x = vval' x) ->
               forall n, eval_pred pval vval p n <-> eval_pred pval vval' p n); simpl; intros.
  - erewrite eval_tm_ext; eauto.
  - apply forall_iff; intro n.
    apply (IHP pval (n, vval) (n, vval')).
    destruct x; asimpl; auto.
  - apply forall_iff; intro Pr.
    apply IHP; destruct x; asimpl; auto.
  - apply impl_iff; firstorder.
  - reflexivity.
  - apply IHP; destruct x; asimpl; auto.
Qed.


Lemma eval_ext' : forall P pval pval' vval,
    (forall X, pval X = pval' X) ->
    eval_prop pval vval P <-> eval_prop pval' vval P.
Proof.
  intros P.
  induction P using prop_pred_ind with
    (P0 := fun p => forall pval pval' vval,
               (forall x, pval x = pval' x) ->
               forall n, eval_pred pval vval p n <-> eval_pred pval' vval p n); simpl; intros.
  - eauto.
  - apply forall_iff; intro n.
    apply IHP;
    destruct X; asimpl; auto.
  - apply forall_iff; intro Pr.
    apply IHP; destruct X; asimpl; auto.
  - apply impl_iff; firstorder.
  - rewrite H; reflexivity.
  - apply IHP; destruct X; asimpl; auto.
Qed.

Check eval_prop.
Print PVal.

Lemma eval_ext'' : forall P pval pval' vval,
    (forall X n, pval X n <-> pval' X n) ->
    eval_prop pval vval P <-> eval_prop pval' vval P.
Proof.
  intros P.
  induction P using prop_pred_ind with
    (P0 := fun p => forall pval pval' vval,
               (forall X n, pval X n <-> pval' X n) ->
               forall n, eval_pred pval vval p n <-> eval_pred pval' vval p n); simpl; intros.
  - auto.
  - apply forall_iff; intro n.
    apply IHP;
    destruct X; asimpl; auto.
  - apply forall_iff; intro Pr.
    apply IHP; destruct X; asimpl; intros; auto; reflexivity.
  - apply impl_iff; firstorder.
  - rewrite H; reflexivity.
  - apply IHP; destruct X; asimpl; auto.
Qed.


Lemma eval_tm_ren : forall t vval ξ,
    eval_tm vval t⟨ξ⟩ = eval_tm (ξ >> vval) t.
Proof.
  induction t; simpl; asimpl; auto.
Qed.

Lemma eval_ren : forall P pval vval θ ξ,
    eval_prop pval vval P⟨θ; ξ⟩ <-> eval_prop (ξ >> pval) (θ >> vval) P.
Proof.
  induction P using prop_pred_ind
    with (P0 :=
            fun p => forall pval vval θ ξ n,
                eval_pred pval vval p⟨θ; ξ⟩ n <-> eval_pred (ξ >> pval) (θ >> vval) p n); simpl; intros.
  - rewrite eval_tm_ren; auto.
  - apply forall_iff; intros n.
    asimpl.
    rewrite IHP.
    assert (forall x, ((0, θ >> S) >> (n, vval)) x = (n, θ >> vval) x) by (destruct x; auto).
    apply eval_ext; auto.
  - apply forall_iff; intros Pr.
    asimpl.
    rewrite IHP.
    apply eval_ext'; destruct X; asimpl; auto.
  - apply impl_iff; auto.
  - asimpl; reflexivity.
  - asimpl.
    rewrite IHP.
    eapply eval_ext; asimpl; auto.
Qed.

Lemma eval_ren_pred : forall p pval vval θ ξ n,
    eval_pred pval vval p⟨θ; ξ⟩ n <-> eval_pred (ξ >> pval) (θ >> vval) p n.
Proof.
  (* No need to be fancy, since we already have the prop case. *)
  induction p; simpl; intros; asimpl.
  - reflexivity.
  - rewrite eval_ren; asimpl; reflexivity.
Qed.

Lemma eval_tm_subst : forall t vval ξ,
    eval_tm vval t[ξ] = eval_tm (fun n => eval_tm vval (ξ n)) t.
Proof.
  induction t; simpl; asimpl; auto.
Qed.

Lemma eval_ext2 : forall P pval pval' vval vval',
    (forall n, pval n = pval' n) ->
    (forall n, vval n = vval' n) ->
    eval_prop pval vval P <-> eval_prop pval' vval' P.
Proof.
  intros; rewrite eval_ext; eauto.
  rewrite eval_ext'; eauto; reflexivity.
Qed.

Lemma eval_ext2' : forall P pval pval' vval vval',
    (forall n x, pval n x <-> pval' n x) ->
    (forall n, vval n = vval' n) ->
    eval_prop pval vval P <-> eval_prop pval' vval' P.
Proof.
  intros; rewrite eval_ext; eauto.
  rewrite eval_ext''; eauto; reflexivity.
Qed.

Lemma eval_subst : forall P pval vval θ ξ,
    eval_prop pval vval P[θ; ξ] <->
      eval_prop (fun X => eval_pred pval vval (ξ X)) (fun n => eval_tm vval (θ n)) P.
Proof.
  induction P using prop_pred_ind
    with (P0 :=
            fun p => forall pval vval θ ξ n,
                eval_pred pval vval p[θ; ξ] n <-> eval_pred (fun X => eval_pred pval vval (ξ X)) (fun n => eval_tm vval (θ n)) p n); simpl; intros.
  - rewrite eval_tm_subst; auto.
  - apply forall_iff; intros n.
    asimpl.
    rewrite IHP.
    apply eval_ext2'; intros.
    + apply eval_ren_pred.
    + destruct n0; simpl; auto.
      apply eval_tm_ren.
  - apply forall_iff; intros Pr.
    asimpl.
    rewrite IHP.
    apply eval_ext''; destruct X; intros; simpl; asimpl; [reflexivity |].
    apply eval_ren_pred.
  - apply impl_iff; auto.
  - asimpl; reflexivity.
  - asimpl.
    rewrite IHP.
    eapply eval_ext2'; asimpl; intros; simpl.
    + apply eval_ren_pred.
    + destruct n0; simpl; auto.
      apply eval_tm_ren.
Qed.


Lemma lift_validates_tm : forall Γ pval vval n,
    validates pval vval Γ ->
    validates pval (n, vval) (lift_tm Γ).
Proof.
  induction Γ; unfold validates in *; setoid_rewrite Forall_forall; simpl; [contradiction |].
  intros pval vval n ih Q [eq | mem]; subst.
  - apply eval_ren; auto.
  - setoid_rewrite Forall_forall in IHΓ.
    auto.
Qed.


Lemma lift_validates_prop : forall Γ pval vval P,
    validates pval vval Γ ->
    validates (P, pval) vval (lift_prop Γ).
Proof.
  induction Γ; unfold validates in *; setoid_rewrite Forall_forall; simpl; [contradiction |].
  intros pval vval n ih Q [eq | mem]; subst.
  - apply eval_ren; asimpl; auto.
  - setoid_rewrite Forall_forall in IHΓ.
    auto.
Qed.

Search (List.nth_error).

Theorem soundness : forall Γ P, Γ ⊢ P -> Γ ⊧ P.
Proof.
  intros G P d; induction d.
  - unfold "⊧".
    unfold validates; intros.
    rewrite Forall_forall in *.
    apply nth_error_In in e.
    apply H; now auto.
  - intro; simpl.
    intros.
    apply IHd.
    unfold validates in *.
    constructor; auto.
  - unfold "⊧" in *; simpl; intros.
    apply IHd.
    apply lift_validates_tm; auto.
  - unfold "⊧" in *; simpl; intros.
    apply IHd.
    apply lift_validates_prop; auto.
  - unfold "⊧" in *; simpl in *; intros; auto.
  - unfold "⊧" in *; simpl in *; intros; auto.
    apply eval_subst.
    assert (h : forall n, eval_tm vval (t.. n) = ((eval_tm vval (t.. 0)), vval) n).
    { destruct n; asimpl; auto. }
    eapply eval_ext; eauto.
  - unfold "⊧" in *; simpl in *; intros; auto.
    apply eval_subst.
    assert (h : forall X, eval_pred pval vval (Q.. X) = ((eval_pred pval vval (Q.. 0)), pval) X) by (destruct X; asimpl; auto).
    eapply eval_ext'; eauto.
  - unfold "⊧" in *; simpl in *; intros; auto.
    setoid_rewrite eval_subst in IHd.
    assert (h : forall n, eval_tm vval (t.. n) = ((eval_tm vval (t.. 0)), vval) n)
      by (destruct n; asimpl; auto).
    eapply eval_ext; [symmetry; apply h|].
    apply IHd; auto.
  - unfold "⊧" in *; simpl in *; intros.
    rewrite eval_subst; asimpl.
    assert (h : forall n, eval_tm vval (t.. n) = ((eval_tm vval (t.. 0)), vval) n)
      by (destruct n; asimpl; auto).
    eapply eval_ext; [intros; asimpl; apply h|].
    eapply IHd; auto.
  - unfold "⊧" in *; simpl in *.
    intros; exfalso.
    assert (h := H0 (fun n => n <> 0)); simpl in h.
    destruct h; now auto.
  - unfold "⊧" in *; simpl in *.
    simpl; intros.
    assert (h := H0 (fun k => Pr (Nat.pred k))); simpl in h; now auto.
  - unfold "⊧" in *; simpl in *.
    simpl; intros.
    replace (n + 0) with n in H0 by auto; now auto.
  - unfold "⊧" in *; simpl in *.
    simpl; intros.
    replace (n + S n0) with (S (n + n0)) in H0 by auto; now auto.
  - unfold "⊧" in *; simpl in *.
    simpl; intros.
    replace (n * 0) with 0 in H0 by auto; now auto.
  - unfold "⊧" in *; simpl in *.
    simpl; intros.
    Require Import Lia.
    replace (n * S n0) with (n + n * n0) in H0 by lia; now auto.
  (* - unfold "⊧" in *; simpl in *. *)
  (*   simpl; intros. *)
  (*   induction n; now auto. *)
Qed.

Definition eq_dec_tm : forall (t1 t2 : tm), { t1 = t2 } + { t1 <> t2 }.
  decide equality.
  decide equality.
Defined.

(* build some "patternization" so that you can turn terms into substitutions. *)
Fixpoint tm_pattern_at_tm (u : tm) (t : tm) : tm :=
  if eq_dec_tm u t then var_tm 0 else
    match t with
    | var_tm n => var_tm (shift n)
    | Z => t
    | Succ t' => Succ (tm_pattern_at_tm u t')
    | Add t1 t2 => Add (tm_pattern_at_tm u t1) (tm_pattern_at_tm u t2)
    | Mult t1 t2 => Mult (tm_pattern_at_tm u t1) (tm_pattern_at_tm u t2)
    end.

Lemma tm_pattern_at_tm_unfold : forall t u,
    tm_pattern_at_tm u t =
      if eq_dec_tm u t then var_tm 0 else
        match t with
        | var_tm n => var_tm (shift n)
        | Z => t
        | Succ t' => Succ (tm_pattern_at_tm u t')
        | Add t1 t2 => Add (tm_pattern_at_tm u t1) (tm_pattern_at_tm u t2)
        | Mult t1 t2 => Mult (tm_pattern_at_tm u t1) (tm_pattern_at_tm u t2)
        end.
Proof.
  intros; destruct t; reflexivity.
Qed.

Lemma tm_pattern_at_tm_subst : forall u t, t = (tm_pattern_at_tm u t)[u..].
Proof.
  intros u t;
    pose (t' := t).
  revert u; induction t; intros u;
  case_eq (eq_dec_tm u t'); intros e h; unfold t' in h; simpl; try rewrite h; asimpl; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Fixpoint tm_pattern_at (u : tm) (P : prop) : prop :=
  match P with
  | n ∈ P => tm_pattern_at_tm u n ∈ P⟨↑; id⟩
  | FORALL P => FORALL (tm_pattern_at u P)
  | P ⇒ Q => (tm_pattern_at u P) ⇒ (tm_pattern_at u Q)
  (* Fixme: handle these cases? *)
  | _ => P⟨↑; id⟩
  end.


Theorem tm_pattern_at_subst : forall t P, P = (tm_pattern_at t P)[t..;ids].
Proof.
  induction P; try (unfold tm_pattern_at; simpl; asimpl; now auto).
  - unfold tm_pattern_at; asimpl; f_equal; apply tm_pattern_at_tm_subst.
  - simpl; asimpl; f_equal; auto.
  - simpl; asimpl; f_equal; auto.
Qed.


(* This section is useful if we want to avoid an induction *axiom*,
   and use a relative predicate everywhere instead. it has some
   advantages in formalizing realizability. *)
Section Nat_prfs.
Definition Nat (t : tm) := FORALL Z ∈ var_pred 0 ⇒ (all var_tm 0 ∈ var_pred 0 ⇒ (Succ (var_tm 0)) ∈ var_pred 0) ⇒ t ∈ var_pred 0.

Theorem Succ_Nat : forall Γ,
    Γ ⊢ all Nat (var_tm 0) ⇒ Nat (Succ (var_tm 0)).
Proof.
  intros ?; apply forallt_intro.
  apply imp_intro.
  apply forallP_intro.
  repeat apply imp_intro.
  apply imp_elim with (P := var_tm 0 ∈ var_pred 0).
  - rewrite (tm_pattern_at_subst (var_tm 0)); simpl.
    eapply forallt_elim.
    apply (axiom 0); auto.
  - unfold Nat.
    apply imp_elim with (P := (all var_tm 0 ∈ var_pred 0 ⇒ Succ (var_tm 0) ∈ var_pred 0)); [ | apply (axiom 0); auto].
    apply imp_elim with (P := Z ∈ var_pred 0); [ | apply (axiom 1); auto].
    replace (Z ∈ var_pred 0 ⇒ (all var_tm 0 ∈ var_pred 0 ⇒ Succ (var_tm 0) ∈ var_pred 0) ⇒ var_tm 0 ∈ var_pred 0) with
    ((Z ∈ var_pred 0 ⇒ (all var_tm 0 ∈ var_pred 0 ⇒ Succ (var_tm 0) ∈ var_pred 0) ⇒ var_tm 0 ∈ var_pred 0)[ids; (var_pred 0)..]) by auto.
    eapply forallP_elim.
    unfold lift_prop; simpl; asimpl.
    apply (axiom 2); auto.
Qed.

End Nat_prfs.

Theorem eq_refl : forall Γ t, Γ ⊢ t ≃ t.
Proof.
  intros; apply forallP_intro; apply imp_intro.
  apply (axiom 0); now auto.
Qed.

Lemma eq_symm_aux : forall (t1 t2 : nat),
    (forall (P : nat -> Prop), P t1 -> P t2) -> (forall (P : nat -> Prop), P t2 -> P t1).
Proof.
  intros t1 t2 h P.
  apply (h (fun n => P n -> P t1)).
  intros h'; exact h'.
Qed.


Theorem eq_symm : forall Γ,
    Γ ⊢ all all var_tm 1 ≃ var_tm 0 ⇒ var_tm 0 ≃ var_tm 1.
Proof.
  intros; repeat apply forallt_intro; apply imp_intro;
    apply forallP_intro; simpl; asimpl.
  pose (S := {{ _ | var_tm 0 ∈ var_pred 0 ⇒ var_tm 2 ∈ var_pred 0}}).
  apply imp_elim with (P := (var_tm 1 ∈ var_pred 0 ⇒ var_tm 0 ∈ var_pred 0)[ids; S..]).
  - unfold S.
    asimpl.
    apply imp_intro.
    rewrite (tm_pattern_at_subst (var_tm 0)); simpl.
    apply compr_elim; asimpl; unfold shift.
    eapply imp_elim; [apply (axiom 0); now eauto|].
    apply compr_intro; asimpl.
    apply imp_intro; apply (axiom 0); auto.
  - eapply forallP_elim; apply (axiom 0); auto.
Qed.

Theorem eq_trans : forall Γ,
    Γ ⊢ all all all var_tm 0 ≃ var_tm 1 ⇒ var_tm 1 ≃ var_tm 2 ⇒ var_tm 0 ≃ var_tm 2.
Proof.
  intro Γ.
  repeat apply forallt_intro.
  repeat apply imp_intro.
  apply forallP_intro.
  apply imp_intro.
  unfold lift_prop; simpl; asimpl.
  apply imp_elim with (P := var_tm 1 ∈ var_pred 0).
  - replace (var_tm 1 ∈ var_pred 0 ⇒ var_tm 2 ∈ var_pred 0) with
      ((var_tm 1 ∈ var_pred 0 ⇒ var_tm 2 ∈ var_pred 0)[ids; (var_pred 0)..]) by auto.
    apply forallP_elim.
    apply (axiom 1); auto.
  - apply imp_elim with (P := var_tm 0 ∈ var_pred 0).
    + replace (var_tm 0 ∈ var_pred 0 ⇒ var_tm 1 ∈ var_pred 0) with
      ((var_tm 0 ∈ var_pred 0 ⇒ var_tm 1 ∈ var_pred 0)[ids; (var_pred 0)..]) by auto.
      apply forallP_elim.
      apply (axiom 2); auto.
    + apply (axiom 0); auto.
Qed.

Lemma tm_pattern_at_impl : forall P Q u, tm_pattern_at u (P ⇒ Q) = (tm_pattern_at u P) ⇒ (tm_pattern_at u Q).
Proof.
  intros; reflexivity.
Qed.

Lemma tm_pattern_at_eq : forall t1 t2 u, tm_pattern_at u (t1 ≃ t2) = (tm_pattern_at_tm u t1) ≃ (tm_pattern_at_tm u t2).
Proof.
  intros; reflexivity.
Qed.

Ltac pattac u := (rewrite (tm_pattern_at_subst u); repeat rewrite tm_pattern_at_impl, tm_pattern_at_eq).

Ltac pattmtac t u := rewrite (tm_pattern_at_tm_subst t u).

Lemma sym_apply : forall Γ t1 t2,
    Γ ⊢ t1 ≃ t2 -> Γ ⊢ t2 ≃ t1.
Proof.
  intros.
  apply imp_elim with (P := t1 ≃ t2); auto.
  Check eq_symm.
  replace (t1 ≃ t2 ⇒ t2 ≃ t1) with (t1⟨↑⟩ ≃ var_tm 0 ⇒ var_tm 0 ≃ t1⟨↑⟩)[t2..; ids] by (asimpl; auto).
  apply forallt_elim.
  replace (all t1 ⟨↑⟩ ≃ var_tm 0 ⇒ var_tm 0 ≃ t1 ⟨↑⟩) with ((all var_tm 1 ≃ var_tm 0 ⇒ var_tm 0 ≃ var_tm 1)[t1..;ids]) by (asimpl; auto).
  apply forallt_elim.
  apply eq_symm.
Qed.

Lemma subst_ren : forall t ξ, t⟨ξ⟩ = t[ξ >> var_tm].
Proof.
  induction t; simpl; asimpl; auto; intros; f_equal; try rewrite IHt1; try rewrite IHt2; auto.
Qed.

Lemma trans_apply : forall Γ t1 t2 t3,
    Γ ⊢ t1 ≃ t2 -> Γ ⊢ t2 ≃ t3 -> Γ ⊢ t1 ≃ t3.
Proof.
  intros.
  apply imp_elim with (P := t2 ≃ t3); auto.
  apply imp_elim with (P := t1 ≃ t2); auto.
  Check eq_trans.
  replace (t1 ≃ t2 ⇒ t2 ≃ t3 ⇒ t1 ≃ t3) with (var_tm 0 ≃ t2⟨↑⟩ ⇒ t2⟨↑⟩ ≃ t3⟨↑⟩ ⇒ var_tm 0 ≃ t3⟨↑⟩)[t1..;ids] by (asimpl; auto); apply forallt_elim.
  replace (all var_tm 0 ≃ t2⟨↑⟩ ⇒ t2⟨↑⟩ ≃ t3⟨↑⟩ ⇒ var_tm 0 ≃ t3⟨↑⟩) with (all var_tm 0 ≃ var_tm 1 ⇒ var_tm 1 ≃ t3⟨↑⟩⟨↑⟩ ⇒ var_tm 0 ≃ t3⟨↑⟩⟨↑⟩)[t2..;ids] by
    (asimpl; repeat rewrite <- subst_ren; auto).
  apply forallt_elim.
  replace (all (all var_tm 0 ≃ var_tm 1 ⇒ var_tm 1 ≃ t3 ⟨↑⟩ ⟨↑⟩ ⇒ var_tm 0 ≃ t3 ⟨↑⟩ ⟨↑⟩)) with
    (all (all var_tm 0 ≃ var_tm 1 ⇒ var_tm 1 ≃ var_tm 2 ⇒ var_tm 0 ≃ var_tm 2))[t3..;ids] by (asimpl; auto).
  apply forallt_elim.
  apply eq_trans.
Qed.



Lemma succ_eq :  forall Γ, Γ ⊢ all all var_tm 0 ≃ var_tm 1 ⇒ Succ (var_tm 0) ≃ Succ (var_tm 1).
Proof.
  intros.
  repeat apply forallt_intro.
  apply imp_intro.
  Locate "≃".
  pattac (var_tm 1).
  eapply compr_elim.
  rewrite tm_pattern_at_eq; simpl.
  apply imp_elim with (P := var_tm 0 ∈ ({{ _ | Succ (var_tm (↑ 0)) ≃ Succ (var_tm 0)}})).
  - replace (var_tm 0 ∈ ({{ _ | Succ (var_tm (↑ 0)) ≃ Succ (var_tm 0)}})
                 ⇒ var_tm 1 ∈ ({{ _ | Succ (var_tm (↑ 0)) ≃ Succ (var_tm 0)}}))
      with
      ((var_tm 0 ∈ var_pred 0 ⇒ var_tm 1 ∈ var_pred 0)[ids; ({{ _ | Succ (var_tm (↑ 0)) ≃ Succ (var_tm 0)}})..]) by
      (asimpl; auto).
    apply forallP_elim.
    apply (axiom 0); auto.

  - apply compr_intro.
    asimpl; simpl.
    apply eq_refl.
Qed.


(* Probably simplify a lot by moving this up! *)
Lemma eq_subst : forall Γ P t1 t2,
    Γ ⊢ t1 ≃ t2 -> Γ ⊢ P[t1..;ids] -> Γ ⊢ P[t2..;ids].
Proof.
  intros.
  apply compr_elim.
  apply imp_elim with (P := t1 ∈ {{ _ | P }}).
  - replace (t1 ∈ ({{ _ | P}}) ⇒ t2 ∈ ({{ _ | P}})) with
      (t1 ∈ var_pred 0 ⇒ t2 ∈ var_pred 0)[ids; {{_ | P}}..] by (asimpl; auto).
    apply forallP_elim; auto.
  - apply compr_intro; auto.
Qed.


Lemma eq_subt_tm_aux : forall Γ t, Γ ⊢ all all var_tm 0 ≃ var_tm 1 ⇒ t[(var_tm 0)..] ≃ t[(var_tm 1)..].
Proof.
  intros.
  repeat apply forallt_intro.
  apply imp_intro.
  replace (t[(var_tm 0)..] ≃ t[(var_tm 1)..]) with
    (t[(var_tm 0)..]⟨↑⟩ ≃ t)[(var_tm 1)..; ids] by (asimpl; auto).
  eapply eq_subst.
  - apply (axiom 0); simpl; eauto.
  - asimpl.
    apply eq_refl.
Qed.

    
Lemma eq_subt_tm : forall Γ t t1 t2,
    Γ ⊢ t1 ≃ t2 -> Γ ⊢ t[t1..] ≃ t[t2..].
Proof.
  intros.
  (* eapply imp_elim; [| apply H]. *)
  replace (t[t1..] ≃ t[t2..]) with
    (t[t1..]⟨↑⟩ ≃ t⟨↑⟩[(var_tm 0)..] )[t2..; ids] by (asimpl; auto).
  eapply eq_subst; eauto.
  asimpl.
  apply eq_refl.
Qed.


Locate "=".
Print eq.

Search Logic.eq_refl.
Print EqdepFacts.

Lemma eq_dec_eq : forall t, eq_dec_tm t t = left (Logic.eq_refl _).
Proof.
  intros t.
  destruct (eq_dec_tm t t).
  - f_equal.
    Check Eqdep_dec.K_dec_type.
    pattern e at 1.
    apply Eqdep_dec.K_dec_type; auto.
    apply eq_dec_tm.
  - destruct n; auto.
Qed.


Lemma eq_dec_neq : forall t1 t2, t1 <> t2 -> {H | eq_dec_tm t1 t2 = right H}.
Proof.
  intros t1 t2 neq.
  destruct (eq_dec_tm t1 t2); try congruence.
  exists n; auto.
Qed.
        

Lemma tm_pattern_at_tm_eq : forall t, tm_pattern_at_tm t t = var_tm 0.
Proof.
  intros t.
  destruct t; unfold tm_pattern_at_tm; rewrite eq_dec_eq; auto.
Qed.


Lemma succ_apply : forall Γ t1 t2,
    Γ ⊢ t1 ≃ t2 -> Γ ⊢ Succ t1 ≃ Succ t2.
Proof.
  intros.
  pattmtac t1 (Succ t1); simpl.
  edestruct (eq_dec_neq t1 (Succ t1)) as (?, e).
  - clear H;
    induction t1; try congruence.
  - rewrite e.
    rewrite tm_pattern_at_tm_eq.
  pattmtac t2 (Succ t2); simpl.
  edestruct (eq_dec_neq t2 (Succ t2)) as (?, e').
  + clear H;
    induction t2; try congruence.
  + rewrite e'.
    rewrite tm_pattern_at_tm_eq.
    apply eq_subt_tm; auto.
Qed.

(* Exactly Coq.Sorting.Permutation, but in type *)
Require Import List.
Import ListNotations.

Check [].

Inductive Permutation {A : Type} : list A -> list A -> Type :=
| perm_nil: Permutation nil nil
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Require Import Arith.

Let adapt f n :=
 let m := f (S n) in if le_lt_dec m (f 0) then m else Nat.pred m.

Lemma perm_nth_error : forall A (l l' : list A), Permutation l l' -> { f : fin -> fin | forall n, nth_error l' n = nth_error l (f n) }.
Proof.
  intros A l l' p; induction p.
  - exists id.
    intros; simpl; auto.
  - destruct IHp as (f & ih).
    exists (0, f >> ↑).
    induction n; unfold ">>"; simpl; auto.
  - exists (1, 0, ↑ >> ↑ ).
    destruct n; simpl; auto.
    destruct n; simpl; auto.
  - destruct IHp1 as (f & ihf).
    destruct IHp2 as (g & ihg).
    exists (g >> f); unfold ">>"; intros; simpl; auto.
    rewrite ihg.
    rewrite ihf; auto.
Qed.

Theorem ctx_perm : forall Γ P, Γ ⊢ P -> forall Γ', Permutation Γ' Γ -> Γ' ⊢ P.
Proof.
  intros Γ P prf; induction prf; intros.
  - destruct (perm_nth_error _ _ _ H) as (f & h).
    apply (axiom (f n)).
    rewrite <- h; auto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
Admitted.
  

Lemma weakening : forall Γ P Q, Γ ⊢ P -> (Q::Γ) ⊢ P.
Proof.
  intros Γ P Q prf; revert Q; induction prf.
Admitted.
  
