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

Section term.
Inductive term  : Type :=
  | var_term : ( fin ) -> term 
  | App : ( term   ) -> ( term   ) -> term 
  | Abs : ( term   ) -> term .

Lemma congr_App  { s0 : term   } { s1 : term   } { t0 : term   } { t1 : term   } (H1 : s0 = t0) (H2 : s1 = t1) : App  s0 s1 = App  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Abs  { s0 : term   } { t0 : term   } (H1 : s0 = t0) : Abs  s0 = Abs  t0 .
Proof. congruence. Qed.

Definition upRen_term_term   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_term   (xiterm : ( fin ) -> fin) (s : term ) : term  :=
    match s return term  with
    | var_term  s => (var_term ) (xiterm s)
    | App  s0 s1 => App  ((ren_term xiterm) s0) ((ren_term xiterm) s1)
    | Abs  s0 => Abs  ((ren_term (upRen_term_term xiterm)) s0)
    end.

Definition up_term_term   (sigma : ( fin ) -> term ) : ( fin ) -> term  :=
  (scons) ((var_term ) (var_zero)) ((funcomp) (ren_term (shift)) sigma).

Fixpoint subst_term   (sigmaterm : ( fin ) -> term ) (s : term ) : term  :=
    match s return term  with
    | var_term  s => sigmaterm s
    | App  s0 s1 => App  ((subst_term sigmaterm) s0) ((subst_term sigmaterm) s1)
    | Abs  s0 => Abs  ((subst_term (up_term_term sigmaterm)) s0)
    end.

Definition upId_term_term  (sigma : ( fin ) -> term ) (Eq : forall x, sigma x = (var_term ) x) : forall x, (up_term_term sigma) x = (var_term ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_term  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : term ) : subst_term sigmaterm s = s :=
    match s return subst_term sigmaterm s = s with
    | var_term  s => Eqterm s
    | App  s0 s1 => congr_App ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term sigmaterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((idSubst_term (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s0)
    end.

Definition upExtRen_term_term   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_term_term xi) x = (upRen_term_term zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_term   (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (Eqterm : forall x, xiterm x = zetaterm x) (s : term ) : ren_term xiterm s = ren_term zetaterm s :=
    match s return ren_term xiterm s = ren_term zetaterm s with
    | var_term  s => (ap) (var_term ) (Eqterm s)
    | App  s0 s1 => congr_App ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term xiterm zetaterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((extRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s0)
    end.

Definition upExt_term_term   (sigma : ( fin ) -> term ) (tau : ( fin ) -> term ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_term sigma) x = (up_term_term tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_term   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : term ) : subst_term sigmaterm s = subst_term tauterm s :=
    match s return subst_term sigmaterm s = subst_term tauterm s with
    | var_term  s => Eqterm s
    | App  s0 s1 => congr_App ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term sigmaterm tauterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((ext_term (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s0)
    end.

Definition up_ren_ren_term_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_term_term tau) (upRen_term_term xi)) x = (upRen_term_term theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_term    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (rhoterm : ( fin ) -> fin) (Eqterm : forall x, ((funcomp) zetaterm xiterm) x = rhoterm x) (s : term ) : ren_term zetaterm (ren_term xiterm s) = ren_term rhoterm s :=
    match s return ren_term zetaterm (ren_term xiterm s) = ren_term rhoterm s with
    | var_term  s => (ap) (var_term ) (Eqterm s)
    | App  s0 s1 => congr_App ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((compRenRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s0)
    end.

Definition up_ren_subst_term_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> term ) (theta : ( fin ) -> term ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_term_term tau) (upRen_term_term xi)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_term    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) tauterm xiterm) x = thetaterm x) (s : term ) : subst_term tauterm (ren_term xiterm s) = subst_term thetaterm s :=
    match s return subst_term tauterm (ren_term xiterm s) = subst_term thetaterm s with
    | var_term  s => Eqterm s
    | App  s0 s1 => congr_App ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((compRenSubst_term (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s0)
    end.

Definition up_subst_ren_term_term    (sigma : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (theta : ( fin ) -> term ) (Eq : forall x, ((funcomp) (ren_term zetaterm) sigma) x = theta x) : forall x, ((funcomp) (ren_term (upRen_term_term zetaterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_term (shift) (upRen_term_term zetaterm) ((funcomp) (shift) zetaterm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_term zetaterm (shift) ((funcomp) (shift) zetaterm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_term (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_term    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (ren_term zetaterm) sigmaterm) x = thetaterm x) (s : term ) : ren_term zetaterm (subst_term sigmaterm s) = subst_term thetaterm s :=
    match s return ren_term zetaterm (subst_term sigmaterm s) = subst_term thetaterm s with
    | var_term  s => Eqterm s
    | App  s0 s1 => congr_App ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((compSubstRen_term (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s0)
    end.

Definition up_subst_subst_term_term    (sigma : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (theta : ( fin ) -> term ) (Eq : forall x, ((funcomp) (subst_term tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (up_term_term tauterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_term (shift) (up_term_term tauterm) ((funcomp) (up_term_term tauterm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_term tauterm (shift) ((funcomp) (ren_term (shift)) tauterm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_term (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_term    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s :=
    match s return subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s with
    | var_term  s => Eqterm s
    | App  s0 s1 => congr_App ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((compSubstSubst_term (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s0)
    end.

Definition rinstInst_up_term_term   (xi : ( fin ) -> fin) (sigma : ( fin ) -> term ) (Eq : forall x, ((funcomp) (var_term ) xi) x = sigma x) : forall x, ((funcomp) (var_term ) (upRen_term_term xi)) x = (up_term_term sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_term   (xiterm : ( fin ) -> fin) (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (var_term ) xiterm) x = sigmaterm x) (s : term ) : ren_term xiterm s = subst_term sigmaterm s :=
    match s return ren_term xiterm s = subst_term sigmaterm s with
    | var_term  s => Eqterm s
    | App  s0 s1 => congr_App ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term xiterm sigmaterm Eqterm) s1)
    | Abs  s0 => congr_Abs ((rinst_inst_term (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s0)
    end.

Lemma rinstInst_term   (xiterm : ( fin ) -> fin) : ren_term xiterm = subst_term ((funcomp) (var_term ) xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_term xiterm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_term  : subst_term (var_term ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_term  : @ren_term   (id) = id .
Proof. exact ((eq_trans) (rinstInst_term ((id) (_))) instId_term). Qed.

Lemma varL_term   (sigmaterm : ( fin ) -> term ) : (funcomp) (subst_term sigmaterm) (var_term ) = sigmaterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_term   (xiterm : ( fin ) -> fin) : (funcomp) (ren_term xiterm) (var_term ) = (funcomp) (var_term ) xiterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_term sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_term    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_term tauterm) (subst_term sigmaterm) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmaterm tauterm n)). Qed.

Lemma compRen_term    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (s : term ) : ren_term zetaterm (subst_term sigmaterm s) = subst_term ((funcomp) (ren_term zetaterm) sigmaterm) s .
Proof. exact (compSubstRen_term sigmaterm zetaterm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_term    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_term zetaterm) (subst_term sigmaterm) = subst_term ((funcomp) (ren_term zetaterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_term sigmaterm zetaterm n)). Qed.

Lemma renComp_term    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) (s : term ) : subst_term tauterm (ren_term xiterm s) = subst_term ((funcomp) tauterm xiterm) s .
Proof. exact (compRenSubst_term xiterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_term    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) : (funcomp) (subst_term tauterm) (ren_term xiterm) = subst_term ((funcomp) tauterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_term xiterm tauterm n)). Qed.

Lemma renRen_term    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (s : term ) : ren_term zetaterm (ren_term xiterm s) = ren_term ((funcomp) zetaterm xiterm) s .
Proof. exact (compRenRen_term xiterm zetaterm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_term    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_term zetaterm) (ren_term xiterm) = ren_term ((funcomp) zetaterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_term xiterm zetaterm n)). Qed.

End term.













Global Instance Subst_type   : Subst1 (( fin ) -> type ) (type ) (type ) := @subst_type   .

Global Instance Subst_term   : Subst1 (( fin ) -> term ) (term ) (term ) := @subst_term   .

Global Instance Ren_type   : Ren1 (( fin ) -> fin) (type ) (type ) := @ren_type   .

Global Instance Ren_term   : Ren1 (( fin ) -> fin) (term ) (term ) := @ren_term   .

Global Instance VarInstance_type  : Var (fin) (type ) := @var_type  .

Notation "x '__type'" := (var_type x) (at level 5, format "x __type") : subst_scope.

(* Notation "x '__type'" := (@ids (_) (_) VarInstance_type x) (at level 5, only printing, format "x __type") : subst_scope. *)

Notation "'var'" := (var_type) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_term  : Var (fin) (term ) := @var_term  .

Notation "x '__term'" := (var_term x) (at level 5, format "x __term") : subst_scope.

(* Notation "x '__term'" := (@ids (_) (_) VarInstance_term x) (at level 5, only printing, format "x __term") : subst_scope. *)

Notation "'var'" := (var_term) (only printing, at level 1) : subst_scope.

Class Up_type X Y := up_type : ( X ) -> Y.

Notation "↑__type" := (up_type) (only printing) : subst_scope.

Class Up_term X Y := up_term : ( X ) -> Y.

Notation "↑__term" := (up_term) (only printing) : subst_scope.

Notation "↑__type" := (up_type_type) (only printing) : subst_scope.

Global Instance Up_type_type   : Up_type (_) (_) := @up_type_type   .

Notation "↑__term" := (up_term_term) (only printing) : subst_scope.

Global Instance Up_term_term   : Up_term (_) (_) := @up_term_term   .

(* Notation "s [ sigmatype ]" := (subst_type sigmatype s) (at level 7, left associativity, only printing) : subst_scope. *)

Notation "[ sigmatype ]" := (subst_type sigmatype) (at level 1, left associativity, only printing) : fscope.

(* Notation "s ⟨ xitype ⟩" := (ren_type xitype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xitype ⟩" := (ren_type xitype) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s [ sigmaterm ]" := (subst_term sigmaterm s) (at level 7, left associativity, only printing) : subst_scope. *)

Notation "[ sigmaterm ]" := (subst_term sigmaterm) (at level 1, left associativity, only printing) : fscope.

(* Notation "s ⟨ xiterm ⟩" := (ren_term xiterm s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xiterm ⟩" := (ren_term xiterm) (at level 1, left associativity, only printing) : fscope. *)

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Subst_term,  Ren_type,  Ren_term,  VarInstance_type,  VarInstance_term.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Subst_term,  Ren_type,  Ren_term,  VarInstance_type,  VarInstance_term in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_type| progress rewrite ?compComp_type| progress rewrite ?compComp'_type| progress rewrite ?instId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?rinstId_type| progress rewrite ?compRen_type| progress rewrite ?compRen'_type| progress rewrite ?renComp_type| progress rewrite ?renComp'_type| progress rewrite ?renRen_type| progress rewrite ?renRen'_type| progress rewrite ?rinstId_term| progress rewrite ?compRen_term| progress rewrite ?compRen'_term| progress rewrite ?renComp_term| progress rewrite ?renComp'_term| progress rewrite ?renRen_term| progress rewrite ?renRen'_term| progress rewrite ?varL_type| progress rewrite ?varL_term| progress rewrite ?varLRen_type| progress rewrite ?varLRen_term| progress (unfold up_ren, upRen_type_type, upRen_term_term, up_type_type, up_term_term)| progress (cbn [subst_type subst_term ren_type ren_term])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_type in *| progress rewrite ?compComp_type in *| progress rewrite ?compComp'_type in *| progress rewrite ?instId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?rinstId_type in *| progress rewrite ?compRen_type in *| progress rewrite ?compRen'_type in *| progress rewrite ?renComp_type in *| progress rewrite ?renComp'_type in *| progress rewrite ?renRen_type in *| progress rewrite ?renRen'_type in *| progress rewrite ?rinstId_term in *| progress rewrite ?compRen_term in *| progress rewrite ?compRen'_term in *| progress rewrite ?renComp_term in *| progress rewrite ?renComp'_term in *| progress rewrite ?renRen_term in *| progress rewrite ?renRen'_term in *| progress rewrite ?varL_type in *| progress rewrite ?varL_term in *| progress rewrite ?varLRen_type in *| progress rewrite ?varLRen_term in *| progress (unfold up_ren, upRen_type_type, upRen_term_term, up_type_type, up_term_term in *)| progress (cbn [subst_type subst_term ren_type ren_term] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_type); try repeat (erewrite rinstInst_term).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_type); try repeat (erewrite <- rinstInst_term).
