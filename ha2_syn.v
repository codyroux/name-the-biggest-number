Require Export unscoped.



Section tm.
Inductive tm  : Type :=
  | var_tm : ( fin ) -> tm 
  | Z : tm 
  | Succ : ( tm   ) -> tm 
  | Add : ( tm   ) -> ( tm   ) -> tm 
  | Mult : ( tm   ) -> ( tm   ) -> tm .

Lemma congr_Z  : Z  = Z  .
Proof. congruence. Qed.

Lemma congr_Succ  { s0 : tm   } { t0 : tm   } (H1 : s0 = t0) : Succ  s0 = Succ  t0 .
Proof. congruence. Qed.

Lemma congr_Add  { s0 : tm   } { s1 : tm   } { t0 : tm   } { t1 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) : Add  s0 s1 = Add  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Mult  { s0 : tm   } { s1 : tm   } { t0 : tm   } { t1 : tm   } (H1 : s0 = t0) (H2 : s1 = t1) : Mult  s0 s1 = Mult  t0 t1 .
Proof. congruence. Qed.

Definition upRen_tm_tm   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_tm   (xitm : ( fin ) -> fin) (s : tm ) : tm  :=
    match s return tm  with
    | var_tm  s => (var_tm ) (xitm s)
    | Z   => Z 
    | Succ  s0 => Succ  ((ren_tm xitm) s0)
    | Add  s0 s1 => Add  ((ren_tm xitm) s0) ((ren_tm xitm) s1)
    | Mult  s0 s1 => Mult  ((ren_tm xitm) s0) ((ren_tm xitm) s1)
    end.

Definition up_tm_tm   (sigma : ( fin ) -> tm ) : ( fin ) -> tm  :=
  (scons) ((var_tm ) (var_zero)) ((funcomp) (ren_tm (shift)) sigma).

Fixpoint subst_tm   (sigmatm : ( fin ) -> tm ) (s : tm ) : tm  :=
    match s return tm  with
    | var_tm  s => sigmatm s
    | Z   => Z 
    | Succ  s0 => Succ  ((subst_tm sigmatm) s0)
    | Add  s0 s1 => Add  ((subst_tm sigmatm) s0) ((subst_tm sigmatm) s1)
    | Mult  s0 s1 => Mult  ((subst_tm sigmatm) s0) ((subst_tm sigmatm) s1)
    end.

Definition upId_tm_tm  (sigma : ( fin ) -> tm ) (Eq : forall x, sigma x = (var_tm ) x) : forall x, (up_tm_tm sigma) x = (var_tm ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_tm  (sigmatm : ( fin ) -> tm ) (Eqtm : forall x, sigmatm x = (var_tm ) x) (s : tm ) : subst_tm sigmatm s = s :=
    match s return subst_tm sigmatm s = s with
    | var_tm  s => Eqtm s
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((idSubst_tm sigmatm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((idSubst_tm sigmatm Eqtm) s0) ((idSubst_tm sigmatm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((idSubst_tm sigmatm Eqtm) s0) ((idSubst_tm sigmatm Eqtm) s1)
    end.

Definition upExtRen_tm_tm   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_tm   (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (Eqtm : forall x, xitm x = zetatm x) (s : tm ) : ren_tm xitm s = ren_tm zetatm s :=
    match s return ren_tm xitm s = ren_tm zetatm s with
    | var_tm  s => (ap) (var_tm ) (Eqtm s)
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((extRen_tm xitm zetatm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((extRen_tm xitm zetatm Eqtm) s0) ((extRen_tm xitm zetatm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((extRen_tm xitm zetatm Eqtm) s0) ((extRen_tm xitm zetatm Eqtm) s1)
    end.

Definition upExt_tm_tm   (sigma : ( fin ) -> tm ) (tau : ( fin ) -> tm ) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_tm   (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (Eqtm : forall x, sigmatm x = tautm x) (s : tm ) : subst_tm sigmatm s = subst_tm tautm s :=
    match s return subst_tm sigmatm s = subst_tm tautm s with
    | var_tm  s => Eqtm s
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((ext_tm sigmatm tautm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((ext_tm sigmatm tautm Eqtm) s0) ((ext_tm sigmatm tautm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((ext_tm sigmatm tautm Eqtm) s0) ((ext_tm sigmatm tautm Eqtm) s1)
    end.

Definition up_ren_ren_tm_tm    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm    (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (rhotm : ( fin ) -> fin) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (s : tm ) : ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s :=
    match s return ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s with
    | var_tm  s => (ap) (var_tm ) (Eqtm s)
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((compRenRen_tm xitm zetatm rhotm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) ((compRenRen_tm xitm zetatm rhotm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) ((compRenRen_tm xitm zetatm rhotm Eqtm) s1)
    end.

Definition up_ren_subst_tm_tm    (xi : ( fin ) -> fin) (tau : ( fin ) -> tm ) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_tm    (xitm : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (thetatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (s : tm ) : subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s with
    | var_tm  s => Eqtm s
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((compRenSubst_tm xitm tautm thetatm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) ((compRenSubst_tm xitm tautm thetatm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) ((compRenSubst_tm xitm tautm thetatm Eqtm) s1)
    end.

Definition up_subst_ren_tm_tm    (sigma : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_tm zetatm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_tm (shift) (upRen_tm_tm zetatm) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (shift) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_tm    (sigmatm : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) (thetatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) (ren_tm zetatm) sigmatm) x = thetatm x) (s : tm ) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm  s => Eqtm s
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1)
    end.

Definition up_subst_subst_tm_tm    (sigma : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_tm tautm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_tm (shift) (up_tm_tm tautm) ((funcomp) (up_tm_tm tautm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (shift) ((funcomp) (ren_tm (shift)) tautm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_tm    (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (thetatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) (subst_tm tautm) sigmatm) x = thetatm x) (s : tm ) : subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm  s => Eqtm s
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1)
    end.

Definition rinstInst_up_tm_tm   (xi : ( fin ) -> fin) (sigma : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (var_tm ) xi) x = sigma x) : forall x, ((funcomp) (var_tm ) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_tm   (xitm : ( fin ) -> fin) (sigmatm : ( fin ) -> tm ) (Eqtm : forall x, ((funcomp) (var_tm ) xitm) x = sigmatm x) (s : tm ) : ren_tm xitm s = subst_tm sigmatm s :=
    match s return ren_tm xitm s = subst_tm sigmatm s with
    | var_tm  s => Eqtm s
    | Z   => congr_Z 
    | Succ  s0 => congr_Succ ((rinst_inst_tm xitm sigmatm Eqtm) s0)
    | Add  s0 s1 => congr_Add ((rinst_inst_tm xitm sigmatm Eqtm) s0) ((rinst_inst_tm xitm sigmatm Eqtm) s1)
    | Mult  s0 s1 => congr_Mult ((rinst_inst_tm xitm sigmatm Eqtm) s0) ((rinst_inst_tm xitm sigmatm Eqtm) s1)
    end.

Lemma rinstInst_tm   (xitm : ( fin ) -> fin) : ren_tm xitm = subst_tm ((funcomp) (var_tm ) xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xitm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm  : subst_tm (var_tm ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_tm ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm  : @ren_tm   (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_))) instId_tm). Qed.

Lemma varL_tm   (sigmatm : ( fin ) -> tm ) : (funcomp) (subst_tm sigmatm) (var_tm ) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm   (xitm : ( fin ) -> fin) : (funcomp) (ren_tm xitm) (var_tm ) = (funcomp) (var_tm ) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm    (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (s : tm ) : subst_tm tautm (subst_tm sigmatm s) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) s .
Proof. exact (compSubstSubst_tm sigmatm tautm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm    (sigmatm : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) : (funcomp) (subst_tm tautm) (subst_tm sigmatm) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmatm tautm n)). Qed.

Lemma compRen_tm    (sigmatm : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) (s : tm ) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) s .
Proof. exact (compSubstRen_tm sigmatm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm    (sigmatm : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) : (funcomp) (ren_tm zetatm) (subst_tm sigmatm) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmatm zetatm n)). Qed.

Lemma renComp_tm    (xitm : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (s : tm ) : subst_tm tautm (ren_tm xitm s) = subst_tm ((funcomp) tautm xitm) s .
Proof. exact (compRenSubst_tm xitm tautm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm    (xitm : ( fin ) -> fin) (tautm : ( fin ) -> tm ) : (funcomp) (subst_tm tautm) (ren_tm xitm) = subst_tm ((funcomp) tautm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xitm tautm n)). Qed.

Lemma renRen_tm    (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (s : tm ) : ren_tm zetatm (ren_tm xitm s) = ren_tm ((funcomp) zetatm xitm) s .
Proof. exact (compRenRen_tm xitm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm    (xitm : ( fin ) -> fin) (zetatm : ( fin ) -> fin) : (funcomp) (ren_tm zetatm) (ren_tm xitm) = ren_tm ((funcomp) zetatm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xitm zetatm n)). Qed.

End tm.

Section proppred.
Inductive prop  : Type :=
  | Mem : ( tm   ) -> ( pred    ) -> prop  
  | Forallt : ( prop    ) -> prop  
  | ForallP : ( prop    ) -> prop  
  | Imp : ( prop    ) -> ( prop    ) -> prop  
 with pred  : Type :=
  | var_pred : ( fin ) -> pred  
  | Compr : ( prop    ) -> pred  .

Lemma congr_Mem  { s0 : tm   } { s1 : pred    } { t0 : tm   } { t1 : pred    } (H1 : s0 = t0) (H2 : s1 = t1) : Mem   s0 s1 = Mem   t0 t1 .
Proof. congruence. Qed.

Lemma congr_Forallt  { s0 : prop    } { t0 : prop    } (H1 : s0 = t0) : Forallt   s0 = Forallt   t0 .
Proof. congruence. Qed.

Lemma congr_ForallP  { s0 : prop    } { t0 : prop    } (H1 : s0 = t0) : ForallP   s0 = ForallP   t0 .
Proof. congruence. Qed.

Lemma congr_Imp  { s0 : prop    } { s1 : prop    } { t0 : prop    } { t1 : prop    } (H1 : s0 = t0) (H2 : s1 = t1) : Imp   s0 s1 = Imp   t0 t1 .
Proof. congruence. Qed.

Lemma congr_Compr  { s0 : prop    } { t0 : prop    } (H1 : s0 = t0) : Compr   s0 = Compr   t0 .
Proof. congruence. Qed.

Definition upRen_tm_pred   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  xi.

Definition upRen_pred_tm   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  xi.

Definition upRen_pred_pred   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_prop   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (s : prop  ) : prop   :=
    match s return prop   with
    | Mem   s0 s1 => Mem   ((ren_tm xitm) s0) ((ren_pred xitm xipred) s1)
    | Forallt   s0 => Forallt   ((ren_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred)) s0)
    | ForallP   s0 => ForallP   ((ren_prop (upRen_pred_tm xitm) (upRen_pred_pred xipred)) s0)
    | Imp   s0 s1 => Imp   ((ren_prop xitm xipred) s0) ((ren_prop xitm xipred) s1)
    end
 with ren_pred   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (s : pred  ) : pred   :=
    match s return pred   with
    | var_pred   s => (var_pred  ) (xipred s)
    | Compr   s0 => Compr   ((ren_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred)) s0)
    end.

Definition up_tm_pred   (sigma : ( fin ) -> pred  ) : ( fin ) -> pred   :=
  (funcomp) (ren_pred (shift) (id)) sigma.

Definition up_pred_tm   (sigma : ( fin ) -> tm ) : ( fin ) -> tm  :=
  (funcomp) (ren_tm (id)) sigma.

Definition up_pred_pred   (sigma : ( fin ) -> pred  ) : ( fin ) -> pred   :=
  (scons) ((var_pred  ) (var_zero)) ((funcomp) (ren_pred (id) (shift)) sigma).

Fixpoint subst_prop   (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (s : prop  ) : prop   :=
    match s return prop   with
    | Mem   s0 s1 => Mem   ((subst_tm sigmatm) s0) ((subst_pred sigmatm sigmapred) s1)
    | Forallt   s0 => Forallt   ((subst_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred)) s0)
    | ForallP   s0 => ForallP   ((subst_prop (up_pred_tm sigmatm) (up_pred_pred sigmapred)) s0)
    | Imp   s0 s1 => Imp   ((subst_prop sigmatm sigmapred) s0) ((subst_prop sigmatm sigmapred) s1)
    end
 with subst_pred   (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (s : pred  ) : pred   :=
    match s return pred   with
    | var_pred   s => sigmapred s
    | Compr   s0 => Compr   ((subst_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred)) s0)
    end.

Definition upId_tm_pred  (sigma : ( fin ) -> pred  ) (Eq : forall x, sigma x = (var_pred  ) x) : forall x, (up_tm_pred sigma) x = (var_pred  ) x :=
  fun n => (ap) (ren_pred (shift) (id)) (Eq n).

Definition upId_pred_tm  (sigma : ( fin ) -> tm ) (Eq : forall x, sigma x = (var_tm ) x) : forall x, (up_pred_tm sigma) x = (var_tm ) x :=
  fun n => (ap) (ren_tm (id)) (Eq n).

Definition upId_pred_pred  (sigma : ( fin ) -> pred  ) (Eq : forall x, sigma x = (var_pred  ) x) : forall x, (up_pred_pred sigma) x = (var_pred  ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_pred (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_prop  (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (Eqtm : forall x, sigmatm x = (var_tm ) x) (Eqpred : forall x, sigmapred x = (var_pred  ) x) (s : prop  ) : subst_prop sigmatm sigmapred s = s :=
    match s return subst_prop sigmatm sigmapred s = s with
    | Mem   s0 s1 => congr_Mem ((idSubst_tm sigmatm Eqtm) s0) ((idSubst_pred sigmatm sigmapred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((idSubst_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (upId_tm_tm (_) Eqtm) (upId_tm_pred (_) Eqpred)) s0)
    | ForallP   s0 => congr_ForallP ((idSubst_prop (up_pred_tm sigmatm) (up_pred_pred sigmapred) (upId_pred_tm (_) Eqtm) (upId_pred_pred (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((idSubst_prop sigmatm sigmapred Eqtm Eqpred) s0) ((idSubst_prop sigmatm sigmapred Eqtm Eqpred) s1)
    end
 with idSubst_pred  (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (Eqtm : forall x, sigmatm x = (var_tm ) x) (Eqpred : forall x, sigmapred x = (var_pred  ) x) (s : pred  ) : subst_pred sigmatm sigmapred s = s :=
    match s return subst_pred sigmatm sigmapred s = s with
    | var_pred   s => Eqpred s
    | Compr   s0 => congr_Compr ((idSubst_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (upId_tm_tm (_) Eqtm) (upId_tm_pred (_) Eqpred)) s0)
    end.

Definition upExtRen_tm_pred   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_pred xi) x = (upRen_tm_pred zeta) x :=
  fun n => Eq n.

Definition upExtRen_pred_tm   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_pred_tm xi) x = (upRen_pred_tm zeta) x :=
  fun n => Eq n.

Definition upExtRen_pred_pred   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_pred_pred xi) x = (upRen_pred_pred zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_prop   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (Eqtm : forall x, xitm x = zetatm x) (Eqpred : forall x, xipred x = zetapred x) (s : prop  ) : ren_prop xitm xipred s = ren_prop zetatm zetapred s :=
    match s return ren_prop xitm xipred s = ren_prop zetatm zetapred s with
    | Mem   s0 s1 => congr_Mem ((extRen_tm xitm zetatm Eqtm) s0) ((extRen_pred xitm xipred zetatm zetapred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((extRen_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (upRen_tm_tm zetatm) (upRen_tm_pred zetapred) (upExtRen_tm_tm (_) (_) Eqtm) (upExtRen_tm_pred (_) (_) Eqpred)) s0)
    | ForallP   s0 => congr_ForallP ((extRen_prop (upRen_pred_tm xitm) (upRen_pred_pred xipred) (upRen_pred_tm zetatm) (upRen_pred_pred zetapred) (upExtRen_pred_tm (_) (_) Eqtm) (upExtRen_pred_pred (_) (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((extRen_prop xitm xipred zetatm zetapred Eqtm Eqpred) s0) ((extRen_prop xitm xipred zetatm zetapred Eqtm Eqpred) s1)
    end
 with extRen_pred   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (Eqtm : forall x, xitm x = zetatm x) (Eqpred : forall x, xipred x = zetapred x) (s : pred  ) : ren_pred xitm xipred s = ren_pred zetatm zetapred s :=
    match s return ren_pred xitm xipred s = ren_pred zetatm zetapred s with
    | var_pred   s => (ap) (var_pred  ) (Eqpred s)
    | Compr   s0 => congr_Compr ((extRen_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (upRen_tm_tm zetatm) (upRen_tm_pred zetapred) (upExtRen_tm_tm (_) (_) Eqtm) (upExtRen_tm_pred (_) (_) Eqpred)) s0)
    end.

Definition upExt_tm_pred   (sigma : ( fin ) -> pred  ) (tau : ( fin ) -> pred  ) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_pred sigma) x = (up_tm_pred tau) x :=
  fun n => (ap) (ren_pred (shift) (id)) (Eq n).

Definition upExt_pred_tm   (sigma : ( fin ) -> tm ) (tau : ( fin ) -> tm ) (Eq : forall x, sigma x = tau x) : forall x, (up_pred_tm sigma) x = (up_pred_tm tau) x :=
  fun n => (ap) (ren_tm (id)) (Eq n).

Definition upExt_pred_pred   (sigma : ( fin ) -> pred  ) (tau : ( fin ) -> pred  ) (Eq : forall x, sigma x = tau x) : forall x, (up_pred_pred sigma) x = (up_pred_pred tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_pred (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_prop   (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (Eqtm : forall x, sigmatm x = tautm x) (Eqpred : forall x, sigmapred x = taupred x) (s : prop  ) : subst_prop sigmatm sigmapred s = subst_prop tautm taupred s :=
    match s return subst_prop sigmatm sigmapred s = subst_prop tautm taupred s with
    | Mem   s0 s1 => congr_Mem ((ext_tm sigmatm tautm Eqtm) s0) ((ext_pred sigmatm sigmapred tautm taupred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((ext_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (up_tm_tm tautm) (up_tm_pred taupred) (upExt_tm_tm (_) (_) Eqtm) (upExt_tm_pred (_) (_) Eqpred)) s0)
    | ForallP   s0 => congr_ForallP ((ext_prop (up_pred_tm sigmatm) (up_pred_pred sigmapred) (up_pred_tm tautm) (up_pred_pred taupred) (upExt_pred_tm (_) (_) Eqtm) (upExt_pred_pred (_) (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((ext_prop sigmatm sigmapred tautm taupred Eqtm Eqpred) s0) ((ext_prop sigmatm sigmapred tautm taupred Eqtm Eqpred) s1)
    end
 with ext_pred   (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (Eqtm : forall x, sigmatm x = tautm x) (Eqpred : forall x, sigmapred x = taupred x) (s : pred  ) : subst_pred sigmatm sigmapred s = subst_pred tautm taupred s :=
    match s return subst_pred sigmatm sigmapred s = subst_pred tautm taupred s with
    | var_pred   s => Eqpred s
    | Compr   s0 => congr_Compr ((ext_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (up_tm_tm tautm) (up_tm_pred taupred) (upExt_tm_tm (_) (_) Eqtm) (upExt_tm_pred (_) (_) Eqpred)) s0)
    end.

Definition up_ren_ren_tm_pred    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_pred tau) (upRen_tm_pred xi)) x = (upRen_tm_pred theta) x :=
  Eq.

Definition up_ren_ren_pred_tm    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_pred_tm tau) (upRen_pred_tm xi)) x = (upRen_pred_tm theta) x :=
  Eq.

Definition up_ren_ren_pred_pred    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_pred_pred tau) (upRen_pred_pred xi)) x = (upRen_pred_pred theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_prop    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (rhotm : ( fin ) -> fin) (rhopred : ( fin ) -> fin) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqpred : forall x, ((funcomp) zetapred xipred) x = rhopred x) (s : prop  ) : ren_prop zetatm zetapred (ren_prop xitm xipred s) = ren_prop rhotm rhopred s :=
    match s return ren_prop zetatm zetapred (ren_prop xitm xipred s) = ren_prop rhotm rhopred s with
    | Mem   s0 s1 => congr_Mem ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) ((compRenRen_pred xitm xipred zetatm zetapred rhotm rhopred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((compRenRen_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (upRen_tm_tm zetatm) (upRen_tm_pred zetapred) (upRen_tm_tm rhotm) (upRen_tm_pred rhopred) (up_ren_ren (_) (_) (_) Eqtm) Eqpred) s0)
    | ForallP   s0 => congr_ForallP ((compRenRen_prop (upRen_pred_tm xitm) (upRen_pred_pred xipred) (upRen_pred_tm zetatm) (upRen_pred_pred zetapred) (upRen_pred_tm rhotm) (upRen_pred_pred rhopred) Eqtm (up_ren_ren (_) (_) (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((compRenRen_prop xitm xipred zetatm zetapred rhotm rhopred Eqtm Eqpred) s0) ((compRenRen_prop xitm xipred zetatm zetapred rhotm rhopred Eqtm Eqpred) s1)
    end
 with compRenRen_pred    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (rhotm : ( fin ) -> fin) (rhopred : ( fin ) -> fin) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqpred : forall x, ((funcomp) zetapred xipred) x = rhopred x) (s : pred  ) : ren_pred zetatm zetapred (ren_pred xitm xipred s) = ren_pred rhotm rhopred s :=
    match s return ren_pred zetatm zetapred (ren_pred xitm xipred s) = ren_pred rhotm rhopred s with
    | var_pred   s => (ap) (var_pred  ) (Eqpred s)
    | Compr   s0 => congr_Compr ((compRenRen_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (upRen_tm_tm zetatm) (upRen_tm_pred zetapred) (upRen_tm_tm rhotm) (upRen_tm_pred rhopred) (up_ren_ren (_) (_) (_) Eqtm) Eqpred) s0)
    end.

Definition up_ren_subst_tm_pred    (xi : ( fin ) -> fin) (tau : ( fin ) -> pred  ) (theta : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_pred tau) (upRen_tm_pred xi)) x = (up_tm_pred theta) x :=
  fun n => (ap) (ren_pred (shift) (id)) (Eq n).

Definition up_ren_subst_pred_tm    (xi : ( fin ) -> fin) (tau : ( fin ) -> tm ) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_pred_tm tau) (upRen_pred_tm xi)) x = (up_pred_tm theta) x :=
  fun n => (ap) (ren_tm (id)) (Eq n).

Definition up_ren_subst_pred_pred    (xi : ( fin ) -> fin) (tau : ( fin ) -> pred  ) (theta : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_pred_pred tau) (upRen_pred_pred xi)) x = (up_pred_pred theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_pred (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_prop    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (thetatm : ( fin ) -> tm ) (thetapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqpred : forall x, ((funcomp) taupred xipred) x = thetapred x) (s : prop  ) : subst_prop tautm taupred (ren_prop xitm xipred s) = subst_prop thetatm thetapred s :=
    match s return subst_prop tautm taupred (ren_prop xitm xipred s) = subst_prop thetatm thetapred s with
    | Mem   s0 s1 => congr_Mem ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) ((compRenSubst_pred xitm xipred tautm taupred thetatm thetapred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((compRenSubst_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (up_tm_tm tautm) (up_tm_pred taupred) (up_tm_tm thetatm) (up_tm_pred thetapred) (up_ren_subst_tm_tm (_) (_) (_) Eqtm) (up_ren_subst_tm_pred (_) (_) (_) Eqpred)) s0)
    | ForallP   s0 => congr_ForallP ((compRenSubst_prop (upRen_pred_tm xitm) (upRen_pred_pred xipred) (up_pred_tm tautm) (up_pred_pred taupred) (up_pred_tm thetatm) (up_pred_pred thetapred) (up_ren_subst_pred_tm (_) (_) (_) Eqtm) (up_ren_subst_pred_pred (_) (_) (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((compRenSubst_prop xitm xipred tautm taupred thetatm thetapred Eqtm Eqpred) s0) ((compRenSubst_prop xitm xipred tautm taupred thetatm thetapred Eqtm Eqpred) s1)
    end
 with compRenSubst_pred    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (thetatm : ( fin ) -> tm ) (thetapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqpred : forall x, ((funcomp) taupred xipred) x = thetapred x) (s : pred  ) : subst_pred tautm taupred (ren_pred xitm xipred s) = subst_pred thetatm thetapred s :=
    match s return subst_pred tautm taupred (ren_pred xitm xipred s) = subst_pred thetatm thetapred s with
    | var_pred   s => Eqpred s
    | Compr   s0 => congr_Compr ((compRenSubst_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (up_tm_tm tautm) (up_tm_pred taupred) (up_tm_tm thetatm) (up_tm_pred thetapred) (up_ren_subst_tm_tm (_) (_) (_) Eqtm) (up_ren_subst_tm_pred (_) (_) (_) Eqpred)) s0)
    end.

Definition up_subst_ren_tm_pred    (sigma : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (theta : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) (ren_pred zetatm zetapred) sigma) x = theta x) : forall x, ((funcomp) (ren_pred (upRen_tm_tm zetatm) (upRen_tm_pred zetapred)) (up_tm_pred sigma)) x = (up_tm_pred theta) x :=
  fun n => (eq_trans) (compRenRen_pred (shift) (id) (upRen_tm_tm zetatm) (upRen_tm_pred zetapred) ((funcomp) (shift) zetatm) ((funcomp) (id) zetapred) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_pred zetatm zetapred (shift) (id) ((funcomp) (shift) zetatm) ((funcomp) (id) zetapred) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_pred (shift) (id)) (Eq n))).

Definition up_subst_ren_pred_tm    (sigma : ( fin ) -> tm ) (zetatm : ( fin ) -> fin) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_pred_tm zetatm)) (up_pred_tm sigma)) x = (up_pred_tm theta) x :=
  fun n => (eq_trans) (compRenRen_tm (id) (upRen_pred_tm zetatm) ((funcomp) (id) zetatm) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (id) ((funcomp) (id) zetatm) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id)) (Eq n))).

Definition up_subst_ren_pred_pred    (sigma : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (theta : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) (ren_pred zetatm zetapred) sigma) x = theta x) : forall x, ((funcomp) (ren_pred (upRen_pred_tm zetatm) (upRen_pred_pred zetapred)) (up_pred_pred sigma)) x = (up_pred_pred theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_pred (id) (shift) (upRen_pred_tm zetatm) (upRen_pred_pred zetapred) ((funcomp) (id) zetatm) ((funcomp) (shift) zetapred) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_pred zetatm zetapred (id) (shift) ((funcomp) (id) zetatm) ((funcomp) (shift) zetapred) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_pred (id) (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_prop    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (thetatm : ( fin ) -> tm ) (thetapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) (ren_tm zetatm) sigmatm) x = thetatm x) (Eqpred : forall x, ((funcomp) (ren_pred zetatm zetapred) sigmapred) x = thetapred x) (s : prop  ) : ren_prop zetatm zetapred (subst_prop sigmatm sigmapred s) = subst_prop thetatm thetapred s :=
    match s return ren_prop zetatm zetapred (subst_prop sigmatm sigmapred s) = subst_prop thetatm thetapred s with
    | Mem   s0 s1 => congr_Mem ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) ((compSubstRen_pred sigmatm sigmapred zetatm zetapred thetatm thetapred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((compSubstRen_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (upRen_tm_tm zetatm) (upRen_tm_pred zetapred) (up_tm_tm thetatm) (up_tm_pred thetapred) (up_subst_ren_tm_tm (_) (_) (_) Eqtm) (up_subst_ren_tm_pred (_) (_) (_) (_) Eqpred)) s0)
    | ForallP   s0 => congr_ForallP ((compSubstRen_prop (up_pred_tm sigmatm) (up_pred_pred sigmapred) (upRen_pred_tm zetatm) (upRen_pred_pred zetapred) (up_pred_tm thetatm) (up_pred_pred thetapred) (up_subst_ren_pred_tm (_) (_) (_) Eqtm) (up_subst_ren_pred_pred (_) (_) (_) (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((compSubstRen_prop sigmatm sigmapred zetatm zetapred thetatm thetapred Eqtm Eqpred) s0) ((compSubstRen_prop sigmatm sigmapred zetatm zetapred thetatm thetapred Eqtm Eqpred) s1)
    end
 with compSubstRen_pred    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (thetatm : ( fin ) -> tm ) (thetapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) (ren_tm zetatm) sigmatm) x = thetatm x) (Eqpred : forall x, ((funcomp) (ren_pred zetatm zetapred) sigmapred) x = thetapred x) (s : pred  ) : ren_pred zetatm zetapred (subst_pred sigmatm sigmapred s) = subst_pred thetatm thetapred s :=
    match s return ren_pred zetatm zetapred (subst_pred sigmatm sigmapred s) = subst_pred thetatm thetapred s with
    | var_pred   s => Eqpred s
    | Compr   s0 => congr_Compr ((compSubstRen_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (upRen_tm_tm zetatm) (upRen_tm_pred zetapred) (up_tm_tm thetatm) (up_tm_pred thetapred) (up_subst_ren_tm_tm (_) (_) (_) Eqtm) (up_subst_ren_tm_pred (_) (_) (_) (_) Eqpred)) s0)
    end.

Definition up_subst_subst_tm_pred    (sigma : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (theta : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) (subst_pred tautm taupred) sigma) x = theta x) : forall x, ((funcomp) (subst_pred (up_tm_tm tautm) (up_tm_pred taupred)) (up_tm_pred sigma)) x = (up_tm_pred theta) x :=
  fun n => (eq_trans) (compRenSubst_pred (shift) (id) (up_tm_tm tautm) (up_tm_pred taupred) ((funcomp) (up_tm_tm tautm) (shift)) ((funcomp) (up_tm_pred taupred) (id)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_pred tautm taupred (shift) (id) ((funcomp) (ren_tm (shift)) tautm) ((funcomp) (ren_pred (shift) (id)) taupred) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_pred (shift) (id)) (Eq n))).

Definition up_subst_subst_pred_tm    (sigma : ( fin ) -> tm ) (tautm : ( fin ) -> tm ) (theta : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_pred_tm tautm)) (up_pred_tm sigma)) x = (up_pred_tm theta) x :=
  fun n => (eq_trans) (compRenSubst_tm (id) (up_pred_tm tautm) ((funcomp) (up_pred_tm tautm) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (id) ((funcomp) (ren_tm (id)) tautm) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id)) (Eq n))).

Definition up_subst_subst_pred_pred    (sigma : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (theta : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) (subst_pred tautm taupred) sigma) x = theta x) : forall x, ((funcomp) (subst_pred (up_pred_tm tautm) (up_pred_pred taupred)) (up_pred_pred sigma)) x = (up_pred_pred theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_pred (id) (shift) (up_pred_tm tautm) (up_pred_pred taupred) ((funcomp) (up_pred_tm tautm) (id)) ((funcomp) (up_pred_pred taupred) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_pred tautm taupred (id) (shift) ((funcomp) (ren_tm (id)) tautm) ((funcomp) (ren_pred (id) (shift)) taupred) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_pred (id) (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_prop    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (thetatm : ( fin ) -> tm ) (thetapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) (subst_tm tautm) sigmatm) x = thetatm x) (Eqpred : forall x, ((funcomp) (subst_pred tautm taupred) sigmapred) x = thetapred x) (s : prop  ) : subst_prop tautm taupred (subst_prop sigmatm sigmapred s) = subst_prop thetatm thetapred s :=
    match s return subst_prop tautm taupred (subst_prop sigmatm sigmapred s) = subst_prop thetatm thetapred s with
    | Mem   s0 s1 => congr_Mem ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) ((compSubstSubst_pred sigmatm sigmapred tautm taupred thetatm thetapred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((compSubstSubst_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (up_tm_tm tautm) (up_tm_pred taupred) (up_tm_tm thetatm) (up_tm_pred thetapred) (up_subst_subst_tm_tm (_) (_) (_) Eqtm) (up_subst_subst_tm_pred (_) (_) (_) (_) Eqpred)) s0)
    | ForallP   s0 => congr_ForallP ((compSubstSubst_prop (up_pred_tm sigmatm) (up_pred_pred sigmapred) (up_pred_tm tautm) (up_pred_pred taupred) (up_pred_tm thetatm) (up_pred_pred thetapred) (up_subst_subst_pred_tm (_) (_) (_) Eqtm) (up_subst_subst_pred_pred (_) (_) (_) (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((compSubstSubst_prop sigmatm sigmapred tautm taupred thetatm thetapred Eqtm Eqpred) s0) ((compSubstSubst_prop sigmatm sigmapred tautm taupred thetatm thetapred Eqtm Eqpred) s1)
    end
 with compSubstSubst_pred    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (thetatm : ( fin ) -> tm ) (thetapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) (subst_tm tautm) sigmatm) x = thetatm x) (Eqpred : forall x, ((funcomp) (subst_pred tautm taupred) sigmapred) x = thetapred x) (s : pred  ) : subst_pred tautm taupred (subst_pred sigmatm sigmapred s) = subst_pred thetatm thetapred s :=
    match s return subst_pred tautm taupred (subst_pred sigmatm sigmapred s) = subst_pred thetatm thetapred s with
    | var_pred   s => Eqpred s
    | Compr   s0 => congr_Compr ((compSubstSubst_prop (up_tm_tm sigmatm) (up_tm_pred sigmapred) (up_tm_tm tautm) (up_tm_pred taupred) (up_tm_tm thetatm) (up_tm_pred thetapred) (up_subst_subst_tm_tm (_) (_) (_) Eqtm) (up_subst_subst_tm_pred (_) (_) (_) (_) Eqpred)) s0)
    end.

Definition rinstInst_up_tm_pred   (xi : ( fin ) -> fin) (sigma : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) (var_pred  ) xi) x = sigma x) : forall x, ((funcomp) (var_pred  ) (upRen_tm_pred xi)) x = (up_tm_pred sigma) x :=
  fun n => (ap) (ren_pred (shift) (id)) (Eq n).

Definition rinstInst_up_pred_tm   (xi : ( fin ) -> fin) (sigma : ( fin ) -> tm ) (Eq : forall x, ((funcomp) (var_tm ) xi) x = sigma x) : forall x, ((funcomp) (var_tm ) (upRen_pred_tm xi)) x = (up_pred_tm sigma) x :=
  fun n => (ap) (ren_tm (id)) (Eq n).

Definition rinstInst_up_pred_pred   (xi : ( fin ) -> fin) (sigma : ( fin ) -> pred  ) (Eq : forall x, ((funcomp) (var_pred  ) xi) x = sigma x) : forall x, ((funcomp) (var_pred  ) (upRen_pred_pred xi)) x = (up_pred_pred sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_pred (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_prop   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) (var_tm ) xitm) x = sigmatm x) (Eqpred : forall x, ((funcomp) (var_pred  ) xipred) x = sigmapred x) (s : prop  ) : ren_prop xitm xipred s = subst_prop sigmatm sigmapred s :=
    match s return ren_prop xitm xipred s = subst_prop sigmatm sigmapred s with
    | Mem   s0 s1 => congr_Mem ((rinst_inst_tm xitm sigmatm Eqtm) s0) ((rinst_inst_pred xitm xipred sigmatm sigmapred Eqtm Eqpred) s1)
    | Forallt   s0 => congr_Forallt ((rinst_inst_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (up_tm_tm sigmatm) (up_tm_pred sigmapred) (rinstInst_up_tm_tm (_) (_) Eqtm) (rinstInst_up_tm_pred (_) (_) Eqpred)) s0)
    | ForallP   s0 => congr_ForallP ((rinst_inst_prop (upRen_pred_tm xitm) (upRen_pred_pred xipred) (up_pred_tm sigmatm) (up_pred_pred sigmapred) (rinstInst_up_pred_tm (_) (_) Eqtm) (rinstInst_up_pred_pred (_) (_) Eqpred)) s0)
    | Imp   s0 s1 => congr_Imp ((rinst_inst_prop xitm xipred sigmatm sigmapred Eqtm Eqpred) s0) ((rinst_inst_prop xitm xipred sigmatm sigmapred Eqtm Eqpred) s1)
    end
 with rinst_inst_pred   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (Eqtm : forall x, ((funcomp) (var_tm ) xitm) x = sigmatm x) (Eqpred : forall x, ((funcomp) (var_pred  ) xipred) x = sigmapred x) (s : pred  ) : ren_pred xitm xipred s = subst_pred sigmatm sigmapred s :=
    match s return ren_pred xitm xipred s = subst_pred sigmatm sigmapred s with
    | var_pred   s => Eqpred s
    | Compr   s0 => congr_Compr ((rinst_inst_prop (upRen_tm_tm xitm) (upRen_tm_pred xipred) (up_tm_tm sigmatm) (up_tm_pred sigmapred) (rinstInst_up_tm_tm (_) (_) Eqtm) (rinstInst_up_tm_pred (_) (_) Eqpred)) s0)
    end.

Lemma rinstInst_prop   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) : ren_prop xitm xipred = subst_prop ((funcomp) (var_tm ) xitm) ((funcomp) (var_pred  ) xipred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_prop xitm xipred (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_pred   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) : ren_pred xitm xipred = subst_pred ((funcomp) (var_tm ) xitm) ((funcomp) (var_pred  ) xipred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_pred xitm xipred (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma instId_prop  : subst_prop (var_tm ) (var_pred  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_prop (var_tm ) (var_pred  ) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_pred  : subst_pred (var_tm ) (var_pred  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_pred (var_tm ) (var_pred  ) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_prop  : @ren_prop     (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_prop ((id) (_)) ((id) (_))) instId_prop). Qed.

Lemma rinstId_pred  : @ren_pred     (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_pred ((id) (_)) ((id) (_))) instId_pred). Qed.

Lemma varL_pred   (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) : (funcomp) (subst_pred sigmatm sigmapred) (var_pred  ) = sigmapred .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_pred   (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) : (funcomp) (ren_pred xitm xipred) (var_pred  ) = (funcomp) (var_pred  ) xipred .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_prop    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (s : prop  ) : subst_prop tautm taupred (subst_prop sigmatm sigmapred s) = subst_prop ((funcomp) (subst_tm tautm) sigmatm) ((funcomp) (subst_pred tautm taupred) sigmapred) s .
Proof. exact (compSubstSubst_prop sigmatm sigmapred tautm taupred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp_pred    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (s : pred  ) : subst_pred tautm taupred (subst_pred sigmatm sigmapred s) = subst_pred ((funcomp) (subst_tm tautm) sigmatm) ((funcomp) (subst_pred tautm taupred) sigmapred) s .
Proof. exact (compSubstSubst_pred sigmatm sigmapred tautm taupred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_prop    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) : (funcomp) (subst_prop tautm taupred) (subst_prop sigmatm sigmapred) = subst_prop ((funcomp) (subst_tm tautm) sigmatm) ((funcomp) (subst_pred tautm taupred) sigmapred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_prop sigmatm sigmapred tautm taupred n)). Qed.

Lemma compComp'_pred    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) : (funcomp) (subst_pred tautm taupred) (subst_pred sigmatm sigmapred) = subst_pred ((funcomp) (subst_tm tautm) sigmatm) ((funcomp) (subst_pred tautm taupred) sigmapred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_pred sigmatm sigmapred tautm taupred n)). Qed.

Lemma compRen_prop    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (s : prop  ) : ren_prop zetatm zetapred (subst_prop sigmatm sigmapred s) = subst_prop ((funcomp) (ren_tm zetatm) sigmatm) ((funcomp) (ren_pred zetatm zetapred) sigmapred) s .
Proof. exact (compSubstRen_prop sigmatm sigmapred zetatm zetapred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen_pred    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (s : pred  ) : ren_pred zetatm zetapred (subst_pred sigmatm sigmapred s) = subst_pred ((funcomp) (ren_tm zetatm) sigmatm) ((funcomp) (ren_pred zetatm zetapred) sigmapred) s .
Proof. exact (compSubstRen_pred sigmatm sigmapred zetatm zetapred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen'_prop    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) : (funcomp) (ren_prop zetatm zetapred) (subst_prop sigmatm sigmapred) = subst_prop ((funcomp) (ren_tm zetatm) sigmatm) ((funcomp) (ren_pred zetatm zetapred) sigmapred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_prop sigmatm sigmapred zetatm zetapred n)). Qed.

Lemma compRen'_pred    (sigmatm : ( fin ) -> tm ) (sigmapred : ( fin ) -> pred  ) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) : (funcomp) (ren_pred zetatm zetapred) (subst_pred sigmatm sigmapred) = subst_pred ((funcomp) (ren_tm zetatm) sigmatm) ((funcomp) (ren_pred zetatm zetapred) sigmapred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_pred sigmatm sigmapred zetatm zetapred n)). Qed.

Lemma renComp_prop    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (s : prop  ) : subst_prop tautm taupred (ren_prop xitm xipred s) = subst_prop ((funcomp) tautm xitm) ((funcomp) taupred xipred) s .
Proof. exact (compRenSubst_prop xitm xipred tautm taupred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp_pred    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) (s : pred  ) : subst_pred tautm taupred (ren_pred xitm xipred s) = subst_pred ((funcomp) tautm xitm) ((funcomp) taupred xipred) s .
Proof. exact (compRenSubst_pred xitm xipred tautm taupred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp'_prop    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) : (funcomp) (subst_prop tautm taupred) (ren_prop xitm xipred) = subst_prop ((funcomp) tautm xitm) ((funcomp) taupred xipred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_prop xitm xipred tautm taupred n)). Qed.

Lemma renComp'_pred    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (tautm : ( fin ) -> tm ) (taupred : ( fin ) -> pred  ) : (funcomp) (subst_pred tautm taupred) (ren_pred xitm xipred) = subst_pred ((funcomp) tautm xitm) ((funcomp) taupred xipred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_pred xitm xipred tautm taupred n)). Qed.

Lemma renRen_prop    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (s : prop  ) : ren_prop zetatm zetapred (ren_prop xitm xipred s) = ren_prop ((funcomp) zetatm xitm) ((funcomp) zetapred xipred) s .
Proof. exact (compRenRen_prop xitm xipred zetatm zetapred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen_pred    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) (s : pred  ) : ren_pred zetatm zetapred (ren_pred xitm xipred s) = ren_pred ((funcomp) zetatm xitm) ((funcomp) zetapred xipred) s .
Proof. exact (compRenRen_pred xitm xipred zetatm zetapred (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen'_prop    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) : (funcomp) (ren_prop zetatm zetapred) (ren_prop xitm xipred) = ren_prop ((funcomp) zetatm xitm) ((funcomp) zetapred xipred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_prop xitm xipred zetatm zetapred n)). Qed.

Lemma renRen'_pred    (xitm : ( fin ) -> fin) (xipred : ( fin ) -> fin) (zetatm : ( fin ) -> fin) (zetapred : ( fin ) -> fin) : (funcomp) (ren_pred zetatm zetapred) (ren_pred xitm xipred) = ren_pred ((funcomp) zetatm xitm) ((funcomp) zetapred xipred) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_pred xitm xipred zetatm zetapred n)). Qed.

End proppred.























Global Instance Subst_tm   : Subst1 (( fin ) -> tm ) (tm ) (tm ) := @subst_tm   .

Global Instance Subst_prop   : Subst2 (( fin ) -> tm ) (( fin ) -> pred  ) (prop  ) (prop  ) := @subst_prop     .

Global Instance Subst_pred   : Subst2 (( fin ) -> tm ) (( fin ) -> pred  ) (pred  ) (pred  ) := @subst_pred     .

Global Instance Ren_tm   : Ren1 (( fin ) -> fin) (tm ) (tm ) := @ren_tm   .

Global Instance Ren_prop   : Ren2 (( fin ) -> fin) (( fin ) -> fin) (prop  ) (prop  ) := @ren_prop     .

Global Instance Ren_pred   : Ren2 (( fin ) -> fin) (( fin ) -> fin) (pred  ) (pred  ) := @ren_pred     .

Global Instance VarInstance_tm  : Var (fin) (tm ) := @var_tm  .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_pred  : Var (fin) (pred  ) := @var_pred   .

Notation "x '__pred'" := (var_pred x) (at level 5, format "x __pred") : subst_scope.

Notation "x '__pred'" := (@ids (_) (_) VarInstance_pred x) (at level 5, only printing, format "x __pred") : subst_scope.

Notation "'var'" := (var_pred) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : ( X ) -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Class Up_pred X Y := up_pred : ( X ) -> Y.

Notation "↑__pred" := (up_pred) (only printing) : subst_scope.

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm   : Up_tm (_) (_) := @up_tm_tm   .

Notation "↑__tm" := (up_tm_pred) (only printing) : subst_scope.

Global Instance Up_tm_pred   : Up_pred (_) (_) := @up_tm_pred    .

Notation "↑__pred" := (up_pred_tm) (only printing) : subst_scope.

Global Instance Up_pred_tm   : Up_tm (_) (_) := @up_pred_tm   .

Notation "↑__pred" := (up_pred_pred) (only printing) : subst_scope.

Global Instance Up_pred_pred   : Up_pred (_) (_) := @up_pred_pred    .

(* Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmatm ]" := (subst_tm sigmatm) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xitm ⟩" := (ren_tm xitm) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s [ sigmatm ; sigmapred ]" := (subst_prop sigmatm sigmapred s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmatm ; sigmapred ]" := (subst_prop sigmatm sigmapred) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xitm ; xipred ⟩" := (ren_prop xitm xipred s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xitm ; xipred ⟩" := (ren_prop xitm xipred) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s [ sigmatm ; sigmapred ]" := (subst_pred sigmatm sigmapred s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmatm ; sigmapred ]" := (subst_pred sigmatm sigmapred) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xitm ; xipred ⟩" := (ren_pred xitm xipred s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xitm ; xipred ⟩" := (ren_pred xitm xipred) (at level 1, left associativity, only printing) : fscope. *)

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Subst_prop,  Subst_pred,  Ren_tm,  Ren_prop,  Ren_pred,  VarInstance_tm,  VarInstance_pred.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Subst_prop,  Subst_pred,  Ren_tm,  Ren_prop,  Ren_pred,  VarInstance_tm,  VarInstance_pred in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?instId_prop| progress rewrite ?compComp_prop| progress rewrite ?compComp'_prop| progress rewrite ?instId_pred| progress rewrite ?compComp_pred| progress rewrite ?compComp'_pred| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?rinstId_prop| progress rewrite ?compRen_prop| progress rewrite ?compRen'_prop| progress rewrite ?renComp_prop| progress rewrite ?renComp'_prop| progress rewrite ?renRen_prop| progress rewrite ?renRen'_prop| progress rewrite ?rinstId_pred| progress rewrite ?compRen_pred| progress rewrite ?compRen'_pred| progress rewrite ?renComp_pred| progress rewrite ?renComp'_pred| progress rewrite ?renRen_pred| progress rewrite ?renRen'_pred| progress rewrite ?varL_tm| progress rewrite ?varL_pred| progress rewrite ?varLRen_tm| progress rewrite ?varLRen_pred| progress (unfold up_ren, upRen_tm_tm, upRen_tm_pred, upRen_pred_tm, upRen_pred_pred, up_tm_tm, up_tm_pred, up_pred_tm, up_pred_pred)| progress (cbn [subst_tm subst_prop subst_pred ren_tm ren_prop ren_pred])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?instId_prop in *| progress rewrite ?compComp_prop in *| progress rewrite ?compComp'_prop in *| progress rewrite ?instId_pred in *| progress rewrite ?compComp_pred in *| progress rewrite ?compComp'_pred in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?rinstId_prop in *| progress rewrite ?compRen_prop in *| progress rewrite ?compRen'_prop in *| progress rewrite ?renComp_prop in *| progress rewrite ?renComp'_prop in *| progress rewrite ?renRen_prop in *| progress rewrite ?renRen'_prop in *| progress rewrite ?rinstId_pred in *| progress rewrite ?compRen_pred in *| progress rewrite ?compRen'_pred in *| progress rewrite ?renComp_pred in *| progress rewrite ?renComp'_pred in *| progress rewrite ?renRen_pred in *| progress rewrite ?renRen'_pred in *| progress rewrite ?varL_tm in *| progress rewrite ?varL_pred in *| progress rewrite ?varLRen_tm in *| progress rewrite ?varLRen_pred in *| progress (unfold up_ren, upRen_tm_tm, upRen_tm_pred, upRen_pred_tm, upRen_pred_pred, up_tm_tm, up_tm_pred, up_pred_tm, up_pred_pred in *)| progress (cbn [subst_tm subst_prop subst_pred ren_tm ren_prop ren_pred] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm); try repeat (erewrite rinstInst_prop); try repeat (erewrite rinstInst_pred).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm); try repeat (erewrite <- rinstInst_prop); try repeat (erewrite <- rinstInst_pred).
