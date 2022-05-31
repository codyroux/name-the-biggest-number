(* A relatively straightforward formalization of HA^2 *)

(* Require Import Coq.Lists.List. *)
(* Require Import Coq.Strings.String. *)
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

Definition None {A : Type} := @Datatypes.None A.

Definition Some {A : Type} := @Datatypes.Some A.

Definition ctxt := list prop.

Notation "t1 ≃ t2" := (FORALL t1 ∈ var_pred 0 ⇒ t2 ∈ var_pred 0) (at level 20).

(* notionally: ∃ x, Q(x) := ∀ P, (∀ x, Q(x) ⇒ P) ⇒ P *)
Notation "∃ Q" := (FORALL (all Q⟨id; ↑⟩ ⇒ all var_tm 0 ∈ var_pred 0) ⇒ all var_tm 0 ∈ var_pred 0)(at level 10).

Notation "⊥" := (FORALL all var_tm 0 ∈ var_pred 0).
Notation "t ≄ u" := ((t ≃ u) ⇒ ⊥)(at level 20).

Definition lift_prop (Γ : ctxt) : ctxt :=
  List.map (fun P => P⟨id;↑⟩) Γ.

Definition lift_tm (Γ : ctxt) : ctxt :=
  List.map (fun P => P⟨↑; id⟩) Γ.


Inductive derives : ctxt -> prop -> Type :=
| axiom : forall n Γ P, List.nth_error Γ n = Some P -> derives Γ P
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
| zero_S : forall Γ, derives Γ (all Succ (var_tm 0) ≄ Z)
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
  (* FIXME: handle these cases? *)
  | _ => P⟨↑; id⟩
  end.


Theorem tm_pattern_at_subst : forall t P, P = (tm_pattern_at t P)[t..;ids].
Proof.
  induction P; try (unfold tm_pattern_at; simpl; asimpl; now auto).
  - unfold tm_pattern_at; asimpl; f_equal; apply tm_pattern_at_tm_subst.
  - simpl; asimpl; f_equal; auto.
  - simpl; asimpl; f_equal; auto.
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

(* Weakening *)

Inductive Permutation {A : Type} : list A -> list A -> Type :=
| perm_nil: Permutation nil nil
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Hint Constructors Permutation.

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

Lemma map_perm : forall A A' l l' (f : A -> A'), Permutation l l' -> Permutation (list_map f l) (list_map f l').
Proof.
  intros until f.
  intro p; induction p; simpl; eauto.
Qed.

Theorem ctx_perm : forall Γ P, Γ ⊢ P -> forall Γ', Permutation Γ' Γ -> Γ' ⊢ P.
Proof.
  intros Γ P prf; induction prf; intros; try (econstructor; now eauto).
  - destruct (perm_nth_error _ _ _ H) as (f & h).
    apply (axiom (f n)).
    rewrite <- h; auto.
  - apply forallt_intro.
    apply IHprf; apply map_perm; auto.
  - apply forallP_intro.
    apply IHprf; apply map_perm; auto.
Qed.


Lemma weakening : forall Γ P Q, Γ ⊢ P -> (Q::Γ) ⊢ P.
Proof.
  intros Γ P Q prf; revert Q; induction prf; try (econstructor; now eauto); intros.
  - apply (axiom (S n)); simpl; auto.
  - constructor.
    eapply ctx_perm; [apply IHprf | eauto].
Qed.

(* Weakening variables! *)
Theorem lift_derives : forall Γ P, Γ ⊢ P -> forall ξ ζ, List.map (fun P => P⟨ξ; ζ⟩) Γ ⊢ P⟨ξ; ζ⟩.
Proof.
  intros Γ P prf; induction prf; intros; asimpl; try (constructor; now auto).
  - apply (axiom n); auto.
    unfold lift_tm; rewrite nth_error_map.
    rewrite e; auto.
  - constructor.
    apply IHprf.
  - constructor.
    assert (h := IHprf (0, ξ >> S) ζ).
    clear IHprf.
    unfold lift_tm in *.
    rewrite map_map in *; asimpl.
    erewrite map_ext; [ | intros; rewrite renRen_prop; reflexivity].
    erewrite map_ext in h; [apply h |].
    asimpl.
    unfold "↑".
    intros.
    rewrite renRen_prop; asimpl; auto.
  - constructor.
    assert (h := IHprf ξ (0, ζ >> S)); clear IHprf.
    revert h.
    unfold lift_prop.
    repeat rewrite map_map; simpl.
    asimpl.
    erewrite map_ext;
      [| intros; rewrite renRen_prop; reflexivity].
    asimpl.
    intros h; erewrite map_ext; [apply h |].
    intros; rewrite renRen_prop; auto.
  - eapply imp_elim; eauto.
  - asimpl in *.
    replace (subst_prop (ren_tm ξ t, ξ >> var_tm) (ζ >> var_pred) P)
      with (P⟨0, ξ >> S; ζ⟩[t⟨ξ⟩..;ids]) by (asimpl; auto).
    apply forallt_elim; auto.
  - asimpl in *.
    replace (subst_prop (ξ >> var_tm) (ren_pred ξ ζ Q, ζ >> var_pred) P)
      with (P⟨ξ; 0, ζ >> S⟩[ids;Q⟨ξ;ζ⟩..]) by (asimpl; auto).
    apply forallP_elim; auto.
  - apply compr_intro; asimpl.
    assert (subst_prop (ren_tm ξ t, ξ >> var_tm) (ζ >> var_pred) P = ren_prop ξ ζ (subst_prop (t, var_tm) var_pred P)) by (asimpl; auto).
    rewrite H; auto.
  - asimpl in *.
    replace (subst_prop (ren_tm ξ t, ξ >> var_tm) (ζ >> var_pred) P) with
      (P ⟨0, ξ >> S; ζ⟩[t⟨ξ⟩..;ids]) by (asimpl; auto).
    apply compr_elim; auto.
Qed.


(* First order matching for application. Very useful! *)

Inductive Match (A : Type) :=
| Empty : Match A
| Fail : Match A
| Success : A -> Match A.

Arguments Empty {A}.
Arguments Fail {A}.
Arguments Success {A}.


Require Import Coq.Classes.EquivDec.

Generalizable Variable A.

Instance eqdec_tm : EqDec tm eq.
Proof.
  unfold EqDec.
  apply eq_dec_tm.
Defined.


Definition join `{EqDec A eq} (l r : Match A) : Match A :=
  match pair l r with
  | pair Empty r => r
  | pair l Empty => l
  | pair (Success t1) (Success t2) => if t1 == t2 then Success t1 else Fail
  | pair Fail _ => Fail
  | pair _ Fail => Fail
  end.

Eval compute in (Add (var_tm 0) (var_tm 1))[Z..].


(* Slight generalization of scons *)
Definition ncons {X : Type}{var : Var fin X} (level : fin) (x : X) (xi : fin -> X) :=
  fun n =>
    if n <? level then var n
    else if n =? level then x
         else xi (Nat.pred n).

Lemma ncons_0 : forall X (Vinst : Var fin X) x xi k,
    ncons 0 x xi k = scons x xi k.
Proof.
  intros; unfold ncons.
  assert (eq : k <? 0 = false) by auto.
  rewrite eq.
  destruct k; auto.
Qed.

Lemma ncons_scons : forall k level u, (var_tm 0, ncons level u ids >> ren_tm ↑) k = ncons (↑ level) u⟨↑⟩ ids k.
Proof.
  destruct k; try (unfold ncons; simpl; now auto).
  intros; asimpl.
  unfold ncons, "↑"; simpl.
  destruct (Nat.ltb_spec k level).
  - assert (h : S k <? S level = true) by (apply Nat.ltb_lt; lia).
    rewrite h; simpl; auto.
  - assert (h : S k <? S level = false) by (apply Nat.ltb_ge; lia); rewrite h; simpl.
    destruct (Nat.eqb_spec k level); simpl; auto.
    erewrite Nat.lt_succ_pred; eauto.
    assert (level < k) by lia; eauto.
Qed.

Print option_map.

Print option.
Definition option_map2  {A B C : Type} : (A -> B -> C) -> (option A -> option B -> option C) :=
  fun f oa ob =>
    match pair oa ob return option C with
    | pair Init.Datatypes.None _ => None
    | pair _ Init.Datatypes.None => None
    | pair (Init.Datatypes.Some a) (Init.Datatypes.Some b) => Some (f a b)
    end.

Fixpoint lower_tm (level : fin) (t : tm) : option tm := 
  match t with
  | var_tm v => if v <? level then None else Some (var_tm (v - level))
  | Z => Some Z
  | Succ t' => option_map Succ (lower_tm level t')
  | Add t1 t2 => option_map2 Add (lower_tm level t1) (lower_tm level t2)
  | Mult t1 t2 => option_map2 Mult (lower_tm level t1) (lower_tm level t2)
  end.

Definition lift_tm_n (level : fin) (t : tm) : tm :=
  t⟨Nat.iter level ↑⟩.

Lemma lift_tm_n_0 : forall t, lift_tm_n 0 t = t.
Proof.
  unfold lift_tm_n; intros.
  unfold Nat.iter; simpl.
  replace (fun x : fin => x) with (@id fin) by reflexivity; asimpl; auto.
Qed.

Hint Rewrite lift_tm_n_0.

Lemma iter_level_up : forall level n, Nat.iter level ↑ n = n + level.
Proof.
  induction level; unfold "↑"; simpl; auto.
  intros; rewrite IHlevel.
  auto.
Qed.

Lemma lower_zero : forall t, lower_tm 0 t = Some t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1, IHt2; auto.
  repeat f_equal; lia.
Qed.

Lemma lower_lift : forall t level, lower_tm level (lift_tm_n level t) = Some t.
Proof.
  induction t; auto.
  - intros; unfold lift_tm_n; simpl; rewrite iter_level_up.
    assert (h : n + level <? level = false) by (rewrite Nat.ltb_ge; lia); rewrite h.
    repeat f_equal; lia.
  - simpl; intros; rewrite IHt.
    simpl; auto.
  - simpl; intros; rewrite IHt1; rewrite IHt2; simpl; auto.
  - simpl; intros; rewrite IHt1; rewrite IHt2; simpl; auto.
Qed.

Lemma lift_lower : forall t u level, lower_tm level t = Some u -> lift_tm_n level u = t.
Proof.
  induction t; simpl; auto.
  - intros u level; destruct (Nat.ltb_spec n level); [intros h; inversion h|].
    intros e; inversion e; subst.
    unfold lift_tm_n; asimpl; rewrite iter_level_up.
    f_equal; lia.
  - intros ? ? e; inversion e; subst; simpl; auto.
  - intros u level.
    case_eq (lower_tm level t); simpl; [ | intros ? h; inversion h].
    intros u' eq1 eq2; inversion eq2; subst.
    unfold lift_tm_n; asimpl.
    f_equal; apply IHt; auto.
  - intros u level; case_eq (lower_tm level t1); case_eq (lower_tm level t2);
      try (intros ? eq1 ? eq2; try inversion eq1; try inversion eq2); [| intros eq1 eq2; subst; intros eq; inversion eq]. (* ugh *)
    rewrite eq1, eq2; unfold option_map2; simpl.
    intros eq; inversion eq; subst.
    unfold lift_tm_n; asimpl; f_equal; [apply IHt1 | apply IHt2]; auto.
  - intros u level; case_eq (lower_tm level t1); case_eq (lower_tm level t2);
      try (intros ? eq1 ? eq2; try inversion eq1; try inversion eq2); [| intros eq1 eq2; subst; intros eq; inversion eq]. (* ugh *)
    rewrite eq1, eq2; unfold option_map2; simpl.
    intros eq; inversion eq; subst.
    unfold lift_tm_n; asimpl; f_equal; [apply IHt1 | apply IHt2]; auto.
Qed.

Hint Resolve lift_lower.

Definition match_var (level : fin) (v : fin) (t : tm) : Match tm :=
  if v <? level then
    match t with
    | var_tm v' => if v =? v' then Empty
                   else Fail
    | _ => Fail
    end
  else if v =? level then
         match lower_tm level t with
         | Init.Datatypes.Some t =>  Success t
         | None => Fail
         end
       else
         match t with
         | var_tm v' => if v =? shift v' then Empty
                        else Fail
         | _ => Fail
         end.

Eval compute in (match_var 0 1 (var_tm 1)).
Eval compute in (match_var 0 0 (var_tm 1)).
Eval compute in (match_var 3 0 (var_tm 0)).
Eval compute in (match_var 1 1 (var_tm 2)).
Eval compute in (match_var 1 2 (var_tm 1)).
Eval compute in (match_var 1 2 (var_tm 2)).
Eval compute in (match_var 1 2 (var_tm 0)).

(*
  We want:
  match_tm (Add (var_tm 0) (var_tm 1)) (Add Z (var_tm 0)) = Success Z
*)
Fixpoint match_tm (level : fin) (p : tm) (t : tm) : Match tm :=
  match pair p t with
  | pair (var_tm v) t' => match_var level v t
  | pair Z Z => Empty
  | pair (Succ p') (Succ t') => match_tm level p' t'
  | pair (Add p1 p2) (Add t1 t2) =>
      join (match_tm level p1 t1) (match_tm level p2 t2)
  | pair (Mult p1 p2) (Mult t1 t2) =>
      join (match_tm level p1 t1) (match_tm level p2 t2)
  | _ => Fail
  end.

Eval compute in match_tm 0 (Add Z (var_tm 1)) (Add Z (var_tm 0)).
Eval compute in match_tm 0 (Add (var_tm 0) (var_tm 1)) (Add Z (var_tm 0)).
Eval compute in (Add (var_tm 0) (var_tm 1))[Z..].
Eval compute in (var_tm 0)⟨ncons 0 1 id⟩.
Eval compute in (Add Z (var_tm 0))⟨ncons 0 1 id⟩.

Lemma match_var_subst_empty : forall v t level u, match_var level v t = Empty -> (var_tm v)[ncons level u ids] = t.
Proof.
  intros v t level.
  unfold match_var.
  destruct (Nat.ltb_spec v level).
  - destruct t; try congruence.
    destruct (Nat.eqb_spec v n); try congruence; auto.
    unfold ncons.
    subst; rewrite <- (Nat.ltb_lt) in *.
    asimpl.
    rewrite H; simpl; auto.
  - destruct (Nat.eqb_spec v level); try congruence.
    + destruct (lower_tm level t); try congruence.
    + intros u; destruct t; try congruence;
        destruct (Nat.eqb_spec v (↑ n0)); try congruence; subst; asimpl.
      intros _; unfold ncons.
      rewrite <- Nat.ltb_ge in *.
      rewrite H; simpl; auto.
      destruct level; auto.
      assert (h : n0 =? level = false) by (destruct (Nat.eqb_spec n0 level); unfold "↑" in *; lia).
      rewrite h; auto.
Qed.

Lemma match_var_subst_success : forall v t u level, match_var level v t = Success u -> (var_tm v)[ncons level (lift_tm_n level u) ids] = t.
Proof.
  intros v t u level;
    unfold match_var.
  destruct (Nat.ltb_spec v level).
  - destruct t; try congruence; destruct (Nat.eqb_spec v n); congruence.
  - destruct (Nat.eqb_spec v level).
    + case_eq (lower_tm level t); [| congruence].
      intros ? eqt equ; inversion equ; subst; unfold ncons; asimpl.
      destruct (Nat.ltb_spec level level); [ lia |].
      rewrite Nat.eqb_refl; auto.
    + destruct t; try congruence.
      destruct (v =? ↑ n0); congruence.
Qed.


Lemma join_empty_l : forall s1 s2, join s1 s2 = Empty -> s1 = Empty.
Proof.
  destruct s1; destruct s2; unfold join; simpl; try congruence.
  destruct (t == t0); simpl; congruence.
Qed.

Lemma join_empty_r : forall s1 s2, join s1 s2 = Empty -> s2 = Empty.
Proof.
  destruct s1; destruct s2; unfold join; simpl; try congruence.
  destruct (t == t0); simpl; congruence.
Qed.

Lemma join_success : forall s1 s2 u, join s1 s2 = Success u -> (s1 = Empty /\ s2 = Success u) \/ (s1 = Success u /\ s2 = Empty) \/ (s1 = Success u /\ s2 = Success u).
Proof.
  destruct s1; destruct s2 ; unfold join; simpl; try congruence; auto.
  intros; destruct (t == t0); intros; try congruence; auto.
  right; right; auto; split; congruence.
Qed.


Hint Resolve match_var_subst_empty match_var_subst_success join_empty_l join_empty_r.


Theorem match_tm_subst_empty : forall p t level u, match_tm level p t = Empty -> p[ncons level u ids] = t.
Proof.
  induction p; induction t; simpl; try congruence; auto; intros.
  - asimpl; f_equal; auto.
  - asimpl; f_equal.
    + apply IHp1; eauto.
    + apply IHp2; eauto.
  - asimpl; f_equal.
    + apply IHp1; eauto.
    + apply IHp2; eauto.
Qed.

Theorem match_tm_subst_success : forall p t u level, match_tm level p t = Success u -> p[ncons level (lift_tm_n level u) ids] = t.
Proof.
  induction p; induction t; simpl; try congruence; auto.
  - asimpl; intros; f_equal; auto.
  - intros; asimpl; f_equal; destruct (join_success _ _ _ H) as [(H1 , H2)| [(H1, H2) | (H1, H2)]]; try apply match_tm_subst_empty, IHp1, IHp2; auto.
    + apply match_tm_subst_empty; auto.
    + apply match_tm_subst_empty; auto.
  - intros; asimpl; f_equal; destruct (join_success _ _ _ H) as [(H1 , H2)| [(H1, H2) | (H1, H2)]]; try apply match_tm_subst_empty, IHp1, IHp2; auto.
    + apply match_tm_subst_empty; auto.
    + apply match_tm_subst_empty; auto.
Qed.


Fixpoint match_prop level (p : prop) (t : prop) {struct p} : Match tm :=
  match pair p t with
  | pair (n ∈ P) (m ∈ Q) => join (match_tm level n m) (match_pred level P Q)
  | pair (P1 ⇒ P2) (Q1 ⇒ Q2) => join (match_prop level P1 Q1) (match_prop level P2 Q2)
  | pair (FORALL P) (FORALL Q) => match_prop level P Q
  | pair (all P) (all Q) => match_prop (↑ level) P Q
  | _ => Fail
  end
with match_pred level (p : pred) (t : pred) {struct p} : Match tm :=
       match pair p t with
       | pair ({{ _ | P}}) ({{ _ | Q }}) => match_prop (↑ level) P Q
       | pair (var_pred n) (var_pred m) =>
           if n =? m then Empty
           else Fail
       | _ => Fail
       end.

Eval compute in match_tm 0 (Add (var_tm 0) (var_tm 1)) (Add (var_tm 1) (var_tm 0)).

Eval compute in match_prop 0 (Add (var_tm 0) (var_tm 1) ∈ var_pred 0) (Add (var_tm 1) (var_tm 0) ∈ var_pred 0).

Eval compute in match_prop 0 (all (Add (var_tm 0) (var_tm 1) ∈ var_pred 0)) (all (Add (var_tm 0) Z ∈ var_pred 0)).

Eval compute in match_prop 0 (all (Add (var_tm 0) (var_tm 1) ∈ var_pred 0)) (all (Add (var_tm 0) (var_tm 1) ∈ var_pred 0)).

Eval compute in match_prop 0 (all (Add (var_tm 0) (var_tm 1) ∈ var_pred 0)) (all (Add (var_tm 0) (var_tm 0) ∈ var_pred 0)).

Eval compute in (all (Add (var_tm 0) (var_tm 1) ∈ var_pred 0))[(var_tm 1)..; ids] : prop.

Eval compute in (all (Add (var_tm 0) (var_tm 1) ∈ var_pred 0))[(var_tm 0)..; ids] : prop.

Theorem match_subst_empty : forall P Q level u, match_prop level P Q = Empty -> P[ncons level u ids; ids] = Q.
Proof.
  induction P using prop_pred_ind with
    (P0 := fun p => forall Q level u, match_pred level p Q = Empty -> p[ncons level u ids; ids] = Q); destruct Q; simpl; try congruence; asimpl; intros.
  - f_equal; eauto.
    rewrite match_tm_subst_empty with (t := t0); eauto.
  - erewrite ext_prop ; [|intros;  apply ncons_scons | reflexivity].
    erewrite IHP; eauto.
  - asimpl; erewrite IHP; auto.
  - asimpl; erewrite IHP1, IHP2; eauto.
  - destruct (Nat.eqb_spec n n0); congruence.
  - asimpl; erewrite ext_prop ; [|intros;  apply ncons_scons | reflexivity].
    erewrite IHP; auto.
Qed.

Theorem match_subst_empty' : forall P Q level u, match_pred level P Q = Empty -> P[ncons level u ids; ids] = Q.
Proof.
  intros; destruct P; asimpl in *.
  - destruct Q; simpl in *; try congruence.
    destruct (Nat.eqb_spec n n0); congruence.
  - destruct Q; simpl in *; try congruence.
    erewrite ext_prop ; [|intros;  apply ncons_scons | reflexivity].
    erewrite match_subst_empty; eauto.
Qed.


Lemma lift_tm_lift : forall level t, (lift_tm_n level t)⟨↑⟩ = lift_tm_n (↑ level) t.
Proof.
  intros; unfold lift_tm_n.
  asimpl.
  apply extRen_tm.
  induction x; simpl; auto.
Qed.

Theorem match_subst_success : forall P Q level t, match_prop level P Q = Success t -> P[ncons level (lift_tm_n level t) ids; ids] = Q.
Proof.
  induction P using prop_pred_ind with
    (P0 := fun p => forall Q level t, match_pred level p Q = Success t -> p[ncons level (lift_tm_n level t) ids; ids] = Q);
    destruct Q; simpl; try congruence; asimpl; intros.
  - destruct (join_success _ _ _ H) as [(H1, H2) | [(H1, H2) | (H1, H2)]].
    + f_equal; [apply match_tm_subst_empty; auto |].
      apply IHP; auto.
    + f_equal; [apply match_tm_subst_success; auto |apply match_subst_empty'; auto].
    + f_equal; [apply match_tm_subst_success; auto | ].
      apply IHP; auto.
  - erewrite ext_prop ; [|intros; apply ncons_scons | reflexivity].
    rewrite lift_tm_lift.
    rewrite IHP with (Q := Q); eauto.
  - asimpl; erewrite IHP; eauto.
  - destruct (join_success _ _ _ H) as [(H1, H2) | [(H1, H2) | (H1, H2)]].
    + erewrite match_subst_empty; eauto.
      erewrite IHP2; auto.
    + erewrite IHP1; eauto.
      erewrite match_subst_empty; eauto.
    + erewrite IHP1; eauto; erewrite IHP2; eauto.
  - destruct (Nat.eqb_spec n n0); congruence.
  - erewrite ext_prop ; [|intros;  apply ncons_scons | reflexivity].
    rewrite lift_tm_lift.
    erewrite IHP; eauto.
Qed.

(* Only first order for now :| *)
Lemma apply_forallt : forall Γ P Q t, match_prop 0 P Q = Success t -> Γ ⊢ all P -> Γ ⊢ Q.
Proof.
  intros.
  rewrite <- (match_subst_success _ _ _ _ H).
  rewrite lift_tm_n_0.
  erewrite ext_prop; [| intros; rewrite ncons_0; eauto | reflexivity].
  apply forallt_elim; auto.
Qed.

Eval simpl in (forall Q P t, match_prop 0 (all P) Q = t).

(* rather useless:
   You already need to know t1 for this to be useful.
*)
Lemma apply_forallt2 : forall Γ P Q t1 t2,
    match_prop 1 P P[var_tm 0, t1 ⟨↑⟩, ids >> ⟨↑⟩ ; ids] = Success t1
    -> match_prop 0 P[var_tm 0, t1 ⟨↑⟩, ids >> ⟨↑⟩ ; ids] Q = Success t2
    -> Γ ⊢ all (all P) -> Γ ⊢ Q.
Proof.
  intros.
  eapply apply_forallt; eauto.
  eapply apply_forallt; eauto.
  simpl; apply H.
Qed.

Lemma apply_forall_def : forall P P' Q t1 t2,
    match_prop 1 P P' = Success t1
    -> match_prop 0 P' Q = Success t2
    -> P' = P[var_tm 0, t1 ⟨↑⟩, ↑ >> ids ; ids].
Proof.
  intros.
  assert (h1 := match_subst_success _ _ _ _ H).
  assert (h2 := match_subst_success _ _ _ _ H0).
  asimpl.
  subst.
  replace 1 with (↑ 0); auto.
  replace (lift_tm_n (↑ 0) t1) with (t1⟨↑⟩) by reflexivity.
  replace var_tm with (@ids fin tm _) by reflexivity.
  eapply ext_prop; auto; intros.
  rewrite <- ncons_scons; simpl.
  destruct x; simpl; auto.
  asimpl.
  rewrite ncons_0.
  destruct x; auto.
Qed.


(********************************************************************

    Theorems in HA2 start here

********************************************************************)



(* This section is useful if we want to avoid an induction *axiom*,
   and use a relative predicate everywhere instead. it has some
   advantages in formalizing realizability. *)
Section Nat_prfs.
Definition Nat (t : tm) := FORALL Z ∈ var_pred 0 ⇒ (all var_tm 0 ∈ var_pred 0 ⇒ (Succ (var_tm 0)) ∈ var_pred 0) ⇒ t ∈ var_pred 0.

Theorem Z_Nat : forall Γ, Γ ⊢ Nat Z.
Proof.
  intros; apply forallP_intro; repeat apply imp_intro.
  apply (axiom 1); auto.
Qed.

Theorem Succ_Nat : forall Γ,
    Γ ⊢ all Nat (var_tm 0) ⇒ Nat (Succ (var_tm 0)).
Proof.
  intros ?; apply forallt_intro.
  apply imp_intro.
  apply forallP_intro.
  repeat apply imp_intro.
  apply imp_elim with (P := var_tm 0 ∈ var_pred 0).
  - eapply apply_forallt; [| apply (axiom 0); reflexivity].
    reflexivity.
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

Lemma sym_apply : forall Γ t1 t2,
    Γ ⊢ t1 ≃ t2 -> Γ ⊢ t2 ≃ t1.
Proof.
  intros.
  apply imp_elim with (P := t1 ≃ t2); auto.
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


Lemma eq_dec_eq : forall t, eq_dec_tm t t = left (Logic.eq_refl _).
Proof.
  intros t.
  destruct (eq_dec_tm t t).
  - f_equal.
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
