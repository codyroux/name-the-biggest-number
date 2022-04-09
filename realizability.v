Require Import ha2.
Require Import System_F.


Fixpoint prop_to_ty (p : prop) : type :=
  match p with
  | _ ∈ X => pred_to_ty X
  | all p => prop_to_ty p
  (* Little trick here from Proofs and Types to be able to realize empty props *)
  | FORALL p => Forall (Arrow (var_type 0) (prop_to_ty p))
  | p ⇒ q => Arrow (prop_to_ty p) (prop_to_ty q)
  end
with pred_to_ty (p : pred) : type :=
       match p with
       | var_pred X => var_type X
       | {{ _ | p }} => prop_to_ty p
       end.

Notation "[[ P ]]" := (prop_to_ty P).


Variable dummy_inhab_pred : pred -> term.
Variable dummy_inhab_prop : prop -> term.

(* We're stuck here in general: if Q is not closed, there are not
necessarily any such terms. *)
Axiom dummy_inhab_pred_tyrel : forall Γ Q, TyRel Γ (dummy_inhab_pred Q) (pred_to_ty Q).
Axiom dummy_inhab_prop_tyrel : forall Γ Q, TyRel Γ (dummy_inhab_prop Q) (prop_to_ty Q).

Print derives.

Definition tm_id := Abs (Var 0).

Print up_ren.
Check (up_ren id).

(* FIXME: just use autosubst for the terms... *)
Fixpoint ren_term ξ (t : term) : term :=
  match t with
  | Var x => Var (ξ x)
  | App t1 t2 => App (ren_term ξ t1) (ren_term ξ t2)
  | Abs t' => Abs (ren_term (up_ren ξ) t')
  end.

Locate "↑".
Print shift.
Print tm_id.

Print tm_id.
Definition proj2 := Abs (Abs (Var 0)).

Definition proof_to_term : forall {Γ P}, Γ ⊢ P -> term.
Proof.
  intros Γ P prf; induction prf.
  - exact (Var n).
  - refine (Abs _).
    exact IHprf.
  - exact IHprf.
  - refine (Abs _).
    refine (ren_term shift _).
    exact IHprf.
  - refine (App _ _).
    + exact IHprf1.
    + exact IHprf2.
  - exact IHprf.
  - refine (App _ _).
    + exact IHprf.
    + exact (dummy_inhab_pred Q).
  - exact IHprf.
  - exact IHprf.
  - (* the tricky one *)
    exact (dummy_inhab_prop (all Succ (var_tm 0) ≃ Z ⇒ ⊥)).
  - exact tm_id.
  - exact proj2.
  - exact proj2.
  - exact proj2.
  - exact proj2.
Defined.

Print proof_to_term.

Definition hyp_to_ctxt (Γ : ctxt) := List.map (fun P => [[P]]) Γ.

Check hyp_to_ctxt.

Lemma prop_ren : forall P θ ξ, [[ P⟨θ; ξ⟩ ]] = [[ P ]] ⟨ξ⟩.
Proof.
  induction P using prop_pred_ind with (P0 := fun p => forall θ ξ, pred_to_ty p⟨θ; ξ⟩ = (pred_to_ty p)⟨ξ⟩); simpl; auto.
  - intros; asimpl; do 2 f_equal; auto.
  - intros; asimpl; f_equal; auto.
Qed.


Lemma prop_lift : forall P θ, [[ P⟨θ; id⟩ ]] = [[ P ]].
Proof.
  intros; rewrite prop_ren; asimpl; auto.
Qed.

Lemma to_ctx_lift : forall Γ, hyp_to_ctxt (lift_tm Γ) = hyp_to_ctxt Γ.
Proof.
  induction Γ; simpl; auto.
  rewrite prop_lift; f_equal; auto.
Qed.

Lemma to_ctx_lift' : forall Γ, hyp_to_ctxt (lift_prop Γ) = lift_ctx (hyp_to_ctxt Γ).
Proof.
  induction Γ; simpl; auto.
  rewrite prop_ren; f_equal; auto.
Qed.

Definition sub_ctx (ξ : fin -> fin) (Γ Δ : context) := forall n T,
    List.nth_error Γ n = some T -> List.nth_error Δ (ξ n) = some T.

Lemma sub_ctx_map : forall f ξ Γ Δ,
    sub_ctx ξ Γ Δ -> sub_ctx ξ (list_map f Γ) (list_map f Δ).
Proof.
  intros f ξ Γ Δ h.
  unfold sub_ctx in *; intros n T.
  repeat rewrite nth_error_map.
  assert (h' := h n).
  unfold some in *.
  destruct (List.nth_error Γ n); destruct (List.nth_error Δ (ξ n)); simpl; try congruence.
  - assert (h'' := h' t Init.Logic.eq_refl).
    inversion h''; congruence.
  - assert (h'' := h' t Init.Logic.eq_refl).
    congruence.
Qed.
  
    

Lemma TyRel_weak : forall Γ t T,
    TyRel Γ t T -> forall Δ ξ, sub_ctx ξ Γ Δ -> TyRel Δ (ren_term ξ t) T.
Proof.
  intros Γ t T d;
    induction d; simpl; intros; econstructor; auto.
  - apply IHd.
    unfold sub_ctx.
    destruct n; simpl; intros; auto.
  - apply IHd; apply sub_ctx_map; auto.
Qed.


Lemma TyRel_weak' : forall Γ t T,
      TyRel Γ t T -> forall U, TyRel (U :: Γ) (ren_term ↑ t) T.
Proof.
  intros; eapply TyRel_weak; eauto.
  unfold sub_ctx; auto.
Qed.


Print Instances Subst1.
Print Instances Subst2.

Lemma ren_prop_aux : forall P σ ξ, prop_to_ty (P⟨σ; ξ⟩) = (prop_to_ty P) ⟨ξ⟩.
Proof.
  induction P using prop_pred_ind with
    (P0 := fun p => forall σ ξ, pred_to_ty (p⟨σ; ξ⟩) = (pred_to_ty p) ⟨ξ⟩); simpl; intros; asimpl; auto.
  - repeat apply f_equal.
    rewrite IHP; auto.
  - rewrite IHP1; rewrite IHP2; auto.
Qed.

Lemma ren_pred_aux : forall P σ ξ, pred_to_ty (P⟨σ; ξ⟩) = (pred_to_ty P) ⟨ξ⟩.
Proof.
  induction P; simpl; asimpl; auto.
  intros; apply ren_prop_aux.
Qed.

Lemma pred_to_ty_lift : forall v ξ, (up_tm_pred ξ >> pred_to_ty) v = (ξ >> pred_to_ty) v.
Proof.
  unfold up_tm_pred.
  intros; asimpl.
  rewrite ren_pred_aux; asimpl; auto.
Qed.

Lemma pred_to_ty_comp : forall (v : fin), (ids >> pred_to_ty) v = ids v.
Proof.
  destruct v; asimpl; auto.
Qed.

Hint Resolve pred_to_ty_comp.

Lemma prop_to_ty_sub : forall (P : prop) (σ : fin -> tm) (ξ : fin -> pred),
    [[ P[σ; ξ] ]] = [[P]] [ξ >> pred_to_ty].
Proof.
  induction P using prop_pred_ind with
    (P0 := fun p => forall σ ξ, pred_to_ty (p [σ; ξ]) = (pred_to_ty p) [ξ >> pred_to_ty]); simpl; intros; auto.
  - rewrite IHP.
    apply ext_type.
    intros; rewrite pred_to_ty_lift; auto.
  - asimpl.
    rewrite IHP.
    do 2 f_equal; auto.
    apply ext_type; intros; asimpl.
    destruct x; asimpl; auto.
    rewrite <- ren_pred_aux with (σ := id).
    asimpl.
    unfold up_pred_pred; asimpl.
    auto.
  - rewrite IHP1; rewrite IHP2; auto.
  - rewrite IHP.
    apply ext_type; intros; apply pred_to_ty_lift.
Qed.

Theorem prf_to_tm_well_typed : forall  Γ P (p : Γ ⊢ P), TyRel (hyp_to_ctxt Γ) (proof_to_term p) [[P]].
Proof.
  intros ? ?; induction p; simpl in *; try constructor; eauto.
  - unfold hyp_to_ctxt.
    rewrite nth_error_map.
    rewrite e; simpl; auto.
  - rewrite to_ctx_lift in *; auto.
  - rewrite to_ctx_lift' in *.
    apply TyRel_abs.
    apply TyRel_weak'; auto.
  - econstructor; eauto.
  - rewrite prop_to_ty_sub.
    erewrite ext_type; eauto.
    asimpl; auto.
  - rewrite prop_to_ty_sub.
    assert (h: forall v, (Q.. >> pred_to_ty) v = ((pred_to_ty Q) ..) v) by (destruct v; asimpl; auto).
    apply TyRel_app with (ty1 := pred_to_ty Q); [ | apply dummy_inhab_pred_tyrel].
    erewrite ext_type; [| apply h].
    replace (Arrow (pred_to_ty Q) (subst_type (pred_to_ty Q).. [[P]]))
            with ((Arrow (var_type 0) [[P]])[(pred_to_ty Q) ..]); [|asimpl]; auto.
    eapply TyRel_ty_app; auto.
  - rewrite prop_to_ty_sub in *.
    erewrite ext_type in IHp; eauto.
    asimpl in IHp; auto.
  - rewrite prop_to_ty_sub.
    erewrite ext_type; eauto; asimpl; auto.
  - pose (t := (prop_to_ty (all Succ (var_tm 0) ≃ Z ⇒ ⊥))).
    replace (Arrow (Forall (Arrow (var_type 0) (Arrow (var_type 0) (var_type 0)))) (Forall (Arrow (var_type 0) (var_type 0)))) with t by reflexivity.
    apply dummy_inhab_prop_tyrel.
  - constructor; auto.
  - do 3 constructor; auto.
  - do 3 constructor; auto.
  - do 3 constructor; auto.
  - do 3 constructor; auto.
Qed.
