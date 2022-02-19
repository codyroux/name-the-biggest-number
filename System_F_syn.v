Require Export unscoped.



Section type.
Inductive type  : Type :=
  | var_type : ( fin ) -> type 
  | Arrow : ( type   ) -> ( type   ) -> type 
  | Forall : ( type   ) -> type .

Lemma congr_Arrow  { s0 : type   } { s1 : type   } { t0 : type   } { t1 : type   } (H1 : s0 = t0) (H2 : s1 = t1) : Arrow  s0 s1 = Arrow  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Forall  { s0 : type   } { t0 : type   } (H1 : s0 = t0) : Forall  s0 = Forall  t0 .
Proof. congruence. Qed.

Definition upRen_type_type   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_type   (xitype : ( fin ) -> fin) (s : type ) : type  :=
    match s return type  with
    | var_type  s => (var_type ) (xitype s)
    | Arrow  s0 s1 => Arrow  ((ren_type xitype) s0) ((ren_type xitype) s1)
    | Forall  s0 => Forall  ((ren_type (upRen_type_type xitype)) s0)
    end.

Definition up_type_type   (sigma : ( fin ) -> type ) : ( fin ) -> type  :=
  (scons) ((var_type ) (var_zero)) ((funcomp) (ren_type (shift)) sigma).

Fixpoint subst_type   (sigmatype : ( fin ) -> type ) (s : type ) : type  :=
    match s return type  with
    | var_type  s => sigmatype s
    | Arrow  s0 s1 => Arrow  ((subst_type sigmatype) s0) ((subst_type sigmatype) s1)
    | Forall  s0 => Forall  ((subst_type (up_type_type sigmatype)) s0)
    end.

Definition upId_type_type  (sigma : ( fin ) -> type ) (Eq : forall x, sigma x = (var_type ) x) : forall x, (up_type_type sigma) x = (var_type ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_type  (sigmatype : ( fin ) -> type ) (Eqtype : forall x, sigmatype x = (var_type ) x) (s : type ) : subst_type sigmatype s = s :=
    match s return subst_type sigmatype s = s with
    | var_type  s => Eqtype s
    | Arrow  s0 s1 => congr_Arrow ((idSubst_type sigmatype Eqtype) s0) ((idSubst_type sigmatype Eqtype) s1)
    | Forall  s0 => congr_Forall ((idSubst_type (up_type_type sigmatype) (upId_type_type (_) Eqtype)) s0)
    end.

Definition upExtRen_type_type   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_type_type xi) x = (upRen_type_type zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_type   (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (Eqtype : forall x, xitype x = zetatype x) (s : type ) : ren_type xitype s = ren_type zetatype s :=
    match s return ren_type xitype s = ren_type zetatype s with
    | var_type  s => (ap) (var_type ) (Eqtype s)
    | Arrow  s0 s1 => congr_Arrow ((extRen_type xitype zetatype Eqtype) s0) ((extRen_type xitype zetatype Eqtype) s1)
    | Forall  s0 => congr_Forall ((extRen_type (upRen_type_type xitype) (upRen_type_type zetatype) (upExtRen_type_type (_) (_) Eqtype)) s0)
    end.

Definition upExt_type_type   (sigma : ( fin ) -> type ) (tau : ( fin ) -> type ) (Eq : forall x, sigma x = tau x) : forall x, (up_type_type sigma) x = (up_type_type tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_type   (sigmatype : ( fin ) -> type ) (tautype : ( fin ) -> type ) (Eqtype : forall x, sigmatype x = tautype x) (s : type ) : subst_type sigmatype s = subst_type tautype s :=
    match s return subst_type sigmatype s = subst_type tautype s with
    | var_type  s => Eqtype s
    | Arrow  s0 s1 => congr_Arrow ((ext_type sigmatype tautype Eqtype) s0) ((ext_type sigmatype tautype Eqtype) s1)
    | Forall  s0 => congr_Forall ((ext_type (up_type_type sigmatype) (up_type_type tautype) (upExt_type_type (_) (_) Eqtype)) s0)
    end.

Definition up_ren_ren_type_type    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_type_type tau) (upRen_type_type xi)) x = (upRen_type_type theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_type    (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (rhotype : ( fin ) -> fin) (Eqtype : forall x, ((funcomp) zetatype xitype) x = rhotype x) (s : type ) : ren_type zetatype (ren_type xitype s) = ren_type rhotype s :=
    match s return ren_type zetatype (ren_type xitype s) = ren_type rhotype s with
    | var_type  s => (ap) (var_type ) (Eqtype s)
    | Arrow  s0 s1 => congr_Arrow ((compRenRen_type xitype zetatype rhotype Eqtype) s0) ((compRenRen_type xitype zetatype rhotype Eqtype) s1)
    | Forall  s0 => congr_Forall ((compRenRen_type (upRen_type_type xitype) (upRen_type_type zetatype) (upRen_type_type rhotype) (up_ren_ren (_) (_) (_) Eqtype)) s0)
    end.

Definition up_ren_subst_type_type    (xi : ( fin ) -> fin) (tau : ( fin ) -> type ) (theta : ( fin ) -> type ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_type_type tau) (upRen_type_type xi)) x = (up_type_type theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_type    (xitype : ( fin ) -> fin) (tautype : ( fin ) -> type ) (thetatype : ( fin ) -> type ) (Eqtype : forall x, ((funcomp) tautype xitype) x = thetatype x) (s : type ) : subst_type tautype (ren_type xitype s) = subst_type thetatype s :=
    match s return subst_type tautype (ren_type xitype s) = subst_type thetatype s with
    | var_type  s => Eqtype s
    | Arrow  s0 s1 => congr_Arrow ((compRenSubst_type xitype tautype thetatype Eqtype) s0) ((compRenSubst_type xitype tautype thetatype Eqtype) s1)
    | Forall  s0 => congr_Forall ((compRenSubst_type (upRen_type_type xitype) (up_type_type tautype) (up_type_type thetatype) (up_ren_subst_type_type (_) (_) (_) Eqtype)) s0)
    end.

Definition up_subst_ren_type_type    (sigma : ( fin ) -> type ) (zetatype : ( fin ) -> fin) (theta : ( fin ) -> type ) (Eq : forall x, ((funcomp) (ren_type zetatype) sigma) x = theta x) : forall x, ((funcomp) (ren_type (upRen_type_type zetatype)) (up_type_type sigma)) x = (up_type_type theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_type (shift) (upRen_type_type zetatype) ((funcomp) (shift) zetatype) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_type zetatype (shift) ((funcomp) (shift) zetatype) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_type (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_type    (sigmatype : ( fin ) -> type ) (zetatype : ( fin ) -> fin) (thetatype : ( fin ) -> type ) (Eqtype : forall x, ((funcomp) (ren_type zetatype) sigmatype) x = thetatype x) (s : type ) : ren_type zetatype (subst_type sigmatype s) = subst_type thetatype s :=
    match s return ren_type zetatype (subst_type sigmatype s) = subst_type thetatype s with
    | var_type  s => Eqtype s
    | Arrow  s0 s1 => congr_Arrow ((compSubstRen_type sigmatype zetatype thetatype Eqtype) s0) ((compSubstRen_type sigmatype zetatype thetatype Eqtype) s1)
    | Forall  s0 => congr_Forall ((compSubstRen_type (up_type_type sigmatype) (upRen_type_type zetatype) (up_type_type thetatype) (up_subst_ren_type_type (_) (_) (_) Eqtype)) s0)
    end.

Definition up_subst_subst_type_type    (sigma : ( fin ) -> type ) (tautype : ( fin ) -> type ) (theta : ( fin ) -> type ) (Eq : forall x, ((funcomp) (subst_type tautype) sigma) x = theta x) : forall x, ((funcomp) (subst_type (up_type_type tautype)) (up_type_type sigma)) x = (up_type_type theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_type (shift) (up_type_type tautype) ((funcomp) (up_type_type tautype) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_type tautype (shift) ((funcomp) (ren_type (shift)) tautype) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_type (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_type    (sigmatype : ( fin ) -> type ) (tautype : ( fin ) -> type ) (thetatype : ( fin ) -> type ) (Eqtype : forall x, ((funcomp) (subst_type tautype) sigmatype) x = thetatype x) (s : type ) : subst_type tautype (subst_type sigmatype s) = subst_type thetatype s :=
    match s return subst_type tautype (subst_type sigmatype s) = subst_type thetatype s with
    | var_type  s => Eqtype s
    | Arrow  s0 s1 => congr_Arrow ((compSubstSubst_type sigmatype tautype thetatype Eqtype) s0) ((compSubstSubst_type sigmatype tautype thetatype Eqtype) s1)
    | Forall  s0 => congr_Forall ((compSubstSubst_type (up_type_type sigmatype) (up_type_type tautype) (up_type_type thetatype) (up_subst_subst_type_type (_) (_) (_) Eqtype)) s0)
    end.

Definition rinstInst_up_type_type   (xi : ( fin ) -> fin) (sigma : ( fin ) -> type ) (Eq : forall x, ((funcomp) (var_type ) xi) x = sigma x) : forall x, ((funcomp) (var_type ) (upRen_type_type xi)) x = (up_type_type sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_type   (xitype : ( fin ) -> fin) (sigmatype : ( fin ) -> type ) (Eqtype : forall x, ((funcomp) (var_type ) xitype) x = sigmatype x) (s : type ) : ren_type xitype s = subst_type sigmatype s :=
    match s return ren_type xitype s = subst_type sigmatype s with
    | var_type  s => Eqtype s
    | Arrow  s0 s1 => congr_Arrow ((rinst_inst_type xitype sigmatype Eqtype) s0) ((rinst_inst_type xitype sigmatype Eqtype) s1)
    | Forall  s0 => congr_Forall ((rinst_inst_type (upRen_type_type xitype) (up_type_type sigmatype) (rinstInst_up_type_type (_) (_) Eqtype)) s0)
    end.

Lemma rinstInst_type   (xitype : ( fin ) -> fin) : ren_type xitype = subst_type ((funcomp) (var_type ) xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_type xitype (_) (fun n => eq_refl) x)). Qed.

Lemma instId_type  : subst_type (var_type ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_type (var_type ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_type  : @ren_type   (id) = id .
Proof. exact ((eq_trans) (rinstInst_type ((id) (_))) instId_type). Qed.

Lemma varL_type   (sigmatype : ( fin ) -> type ) : (funcomp) (subst_type sigmatype) (var_type ) = sigmatype .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_type   (xitype : ( fin ) -> fin) : (funcomp) (ren_type xitype) (var_type ) = (funcomp) (var_type ) xitype .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_type    (sigmatype : ( fin ) -> type ) (tautype : ( fin ) -> type ) (s : type ) : subst_type tautype (subst_type sigmatype s) = subst_type ((funcomp) (subst_type tautype) sigmatype) s .
Proof. exact (compSubstSubst_type sigmatype tautype (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_type    (sigmatype : ( fin ) -> type ) (tautype : ( fin ) -> type ) : (funcomp) (subst_type tautype) (subst_type sigmatype) = subst_type ((funcomp) (subst_type tautype) sigmatype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_type sigmatype tautype n)). Qed.

Lemma compRen_type    (sigmatype : ( fin ) -> type ) (zetatype : ( fin ) -> fin) (s : type ) : ren_type zetatype (subst_type sigmatype s) = subst_type ((funcomp) (ren_type zetatype) sigmatype) s .
Proof. exact (compSubstRen_type sigmatype zetatype (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_type    (sigmatype : ( fin ) -> type ) (zetatype : ( fin ) -> fin) : (funcomp) (ren_type zetatype) (subst_type sigmatype) = subst_type ((funcomp) (ren_type zetatype) sigmatype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_type sigmatype zetatype n)). Qed.

Lemma renComp_type    (xitype : ( fin ) -> fin) (tautype : ( fin ) -> type ) (s : type ) : subst_type tautype (ren_type xitype s) = subst_type ((funcomp) tautype xitype) s .
Proof. exact (compRenSubst_type xitype tautype (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_type    (xitype : ( fin ) -> fin) (tautype : ( fin ) -> type ) : (funcomp) (subst_type tautype) (ren_type xitype) = subst_type ((funcomp) tautype xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_type xitype tautype n)). Qed.

Lemma renRen_type    (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (s : type ) : ren_type zetatype (ren_type xitype s) = ren_type ((funcomp) zetatype xitype) s .
Proof. exact (compRenRen_type xitype zetatype (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_type    (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) : (funcomp) (ren_type zetatype) (ren_type xitype) = ren_type ((funcomp) zetatype xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_type xitype zetatype n)). Qed.

End type.







Global Instance Subst_type   : Subst1 (( fin ) -> type ) (type ) (type ) := @subst_type   .

Global Instance Ren_type   : Ren1 (( fin ) -> fin) (type ) (type ) := @ren_type   .

Global Instance VarInstance_type  : Var (fin) (type ) := @var_type  .

(* Notation "x '__type'" := (var_type x) (at level 5, format "x __type") : subst_scope. *)

(* Notation "x '__type'" := (@ids (_) (_) VarInstance_type x) (at level 5, only printing, format "x __type") : subst_scope. *)

Notation "'var'" := (var_type) (only printing, at level 1) : subst_scope.

Class Up_type X Y := up_type : ( X ) -> Y.

(* Notation "↑__type" := (up_type) (only printing) : subst_scope. *)

(* Notation "↑__type" := (up_type_type) (only printing) : subst_scope. *)

Global Instance Up_type_type   : Up_type (_) (_) := @up_type_type   .

(* Notation "s [ sigmatype ]" := (subst_type sigmatype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmatype ]" := (subst_type sigmatype) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xitype ⟩" := (ren_type xitype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xitype ⟩" := (ren_type xitype) (at level 1, left associativity, only printing) : fscope. *)

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Ren_type,  VarInstance_type.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Ren_type,  VarInstance_type in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_type| progress rewrite ?compComp_type| progress rewrite ?compComp'_type| progress rewrite ?rinstId_type| progress rewrite ?compRen_type| progress rewrite ?compRen'_type| progress rewrite ?renComp_type| progress rewrite ?renComp'_type| progress rewrite ?renRen_type| progress rewrite ?renRen'_type| progress rewrite ?varL_type| progress rewrite ?varLRen_type| progress (unfold up_ren, upRen_type_type, up_type_type)| progress (cbn [subst_type ren_type])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_type in *| progress rewrite ?compComp_type in *| progress rewrite ?compComp'_type in *| progress rewrite ?rinstId_type in *| progress rewrite ?compRen_type in *| progress rewrite ?compRen'_type in *| progress rewrite ?renComp_type in *| progress rewrite ?renComp'_type in *| progress rewrite ?renRen_type in *| progress rewrite ?renRen'_type in *| progress rewrite ?varL_type in *| progress rewrite ?varLRen_type in *| progress (unfold up_ren, upRen_type_type, up_type_type in *)| progress (cbn [subst_type ren_type] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_type).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_type).
