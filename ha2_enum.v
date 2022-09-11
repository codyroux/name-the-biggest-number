Require Import ha2_refl countable.
Close Scope subst_scope.
Require Import List.

Import ListNotations.

Check [0].
Check [0; 1; 2; 3].

Check @enum_iso.
Print retract.

Print gen_tree.
Print tm.
Locate tm.

Fixpoint tm_to_gen_tree (t : tm) : gen_tree fin :=
  match t with
  | var_tm x => gen_cons 0 ([gen_nil x])
  | Z => gen_cons 1 ([])
  | Succ t => gen_cons 2 ([tm_to_gen_tree t])
  | ha2_syn.Add t1 t2 => gen_cons 3 ([tm_to_gen_tree t1; tm_to_gen_tree t2])
  | Mult t1 t2 => gen_cons 4 ([tm_to_gen_tree t1; tm_to_gen_tree t2])
  end.

Search (_ -> _ -> option _).

Definition bind_opt {A B} (o : option A) (f : A -> option B) : option B :=
  match o with
  | Datatypes.Some a => f a
  | Datatypes.None => @Datatypes.None B
  end.

Definition map_opt {A B} (o : option A) (f : A -> B) : option B :=
  match o with
  | Datatypes.Some a => Some (f a)
  | Datatypes.None => @Datatypes.None B
  end.

Definition map_opt_2 {A B C} (o1 : option A) (o2 : option B) (f : A -> B -> C) : option C :=
  match (pair o1 o2) with
  | pair (Datatypes.Some a) (Datatypes.Some b) => Some (f a b)
  | _ => None
  end.

Fixpoint gen_tree_to_tm (g : gen_tree fin) : option tm :=
  match g with
  | gen_cons 0 ([gen_nil x]) => Some (var_tm x)
  | gen_cons 1 ([]) => Some Z
  | gen_cons 2 ([g']) => map_opt (gen_tree_to_tm g') Succ
  | gen_cons 3 ([g1; g2]) => map_opt_2 (gen_tree_to_tm g1) (gen_tree_to_tm g2) ha2_syn.Add
  | gen_cons 4 ([g1; g2]) => map_opt_2 (gen_tree_to_tm g1) (gen_tree_to_tm g2) Mult
  | _ => None
  end.

Print retract.

Definition retract_tm : retract (gen_tree fin) tm.
Proof.
  refine {| in_A := tm_to_gen_tree; out_A := gen_tree_to_tm |}.
  induction b; simpl; auto.
  - rewrite IHb; auto.
  - rewrite IHb1, IHb2; auto.
  - rewrite IHb1, IHb2; auto.
Defined.

Check @has_depth_iso.


Instance has_depth_tm : has_depth tm.
Proof.
  apply (has_depth_iso retract_tm).
Defined.

Instance enum_tm : enum tm.
Proof.
  apply enum_iso.
Defined.

Print enum.

Eval vm_compute in list_up_to 4 : list tm.

(* Ok let's see if we can do propositions *)
Print gen_tree.
Print prop.

Fixpoint prop_to_gen_tree (p : prop) : gen_tree (tm + fin) :=
  match p with
  | t ∈ pr => gen_cons 0 ([gen_nil (inl t); pred_to_gen_tree pr])
  | all p' => gen_cons 1 ([prop_to_gen_tree p'])
  | FORALL p' => gen_cons 2 ([prop_to_gen_tree p'])
  | p1 ⇒ p2 => gen_cons 3 ([prop_to_gen_tree p1; prop_to_gen_tree p2])
  end
  with pred_to_gen_tree (pr : pred) : gen_tree (tm + fin) :=
    match pr with
    | var_pred v => gen_nil (inr v)
    | {{ _ | p }} => gen_cons 4 ([prop_to_gen_tree p])
    end.

Fixpoint gen_tree_to_prop (g : gen_tree (tm + fin)) : option prop :=
  match g with
  | gen_cons 0 ([gen_nil (inl t); g']) =>
      let pr := gen_tree_to_pred g' in
      map_opt pr (fun pr => t ∈ pr)
  | gen_cons 1 ([g']) =>
      map_opt (gen_tree_to_prop g') (fun p => all p)
  | gen_cons 2 ([g']) =>
      map_opt (gen_tree_to_prop g') (fun p => FORALL p)
  | gen_cons 3 ([g1; g2]) =>
      let p1 := gen_tree_to_prop g1 in
      let p2 := gen_tree_to_prop g2 in
      map_opt_2 p1 p2 (fun p1 p2 => p1 ⇒ p2)
  | _ => None
  end
with gen_tree_to_pred (g : gen_tree (tm + fin)) : option pred :=
       match g with
       | gen_nil (inr v) => Some (var_pred v)
       | gen_cons 4 ([g]) =>
           map_opt (gen_tree_to_prop g) (fun p => {{ _ | p }})
       | _ => None
  end
.

Print Instances enum.

Definition retract_prop : retract (gen_tree (tm + fin)) prop.
Proof.
  refine {|
      in_A := prop_to_gen_tree;
      out_A := gen_tree_to_prop;
    |}.
  intros P.
  induction P using prop_pred_ind with
    (P0 := fun p => gen_tree_to_pred (pred_to_gen_tree p) = Datatypes.Some p);
    simpl; try rewrite IHP; simpl; auto.
  rewrite IHP1, IHP2.
  unfold map_opt_2.
  auto.
Defined.

Definition retract_pred : retract (gen_tree (tm + fin)) pred.
Proof.
  refine {|
      in_A := pred_to_gen_tree;
      out_A := gen_tree_to_pred;
    |}.
  intros P.
  induction P; simpl; auto.
  unfold map_opt.
  Print retract.
  pose (r := (@is_gen_retract _ _ retract_prop)).
  simpl in r.
  rewrite r.
  auto.
Defined.

Goal enum (tm + fin).
  apply _.
Qed.

Instance has_depth_prop : has_depth prop.
Proof.
  eapply @has_depth_iso; eauto.
  - apply (_ : has_depth (gen_tree (tm + fin))).
  - apply retract_prop.
Defined.

Instance has_depth_pred : has_depth pred.
Proof.
  eapply @has_depth_iso; eauto.
  - apply (_ : has_depth (gen_tree (tm + fin))).
  - apply retract_pred.
Defined.

Instance enum_prop : enum prop.
Proof.
  apply enum_iso.
Defined.

Check @list_up_to.

Eval compute in depth (FORALL all var_tm 0 ∈ var_pred 0).

Eval vm_compute in (list_up_to 3: list (gen_tree (fin + tm))).

Eval vm_compute in (list_up_to 3: list prop).

Print derives.

Print Instances enum.

Instance enum_ctxt : enum ctxt.
Proof. apply _. Defined.

Inductive derivation_leaf :=
| Loc : nat -> derivation_leaf
| Ctxt : ctxt -> derivation_leaf
| PropLeaf : prop -> derivation_leaf
| Pred : pred -> derivation_leaf
| Tm : tm -> derivation_leaf.

Fixpoint derives_to_gen_tree {Γ P} (d : Γ ⊢ P) : gen_tree derivation_leaf :=
  match d with
  | axiom n Γ P _ => gen_cons 0 ([
                                    gen_nil (Loc n);
                                    gen_nil (Ctxt Γ)
                                ])
  | imp_intro Γ P Q p => gen_cons 1 ([
                                        gen_nil (Ctxt Γ);
                                        gen_nil (PropLeaf P);
                                        gen_nil (PropLeaf Q);
                                        derives_to_gen_tree p
                                    ])
  | forallt_intro Γ P p => gen_cons 2 ([
                                          gen_nil (Ctxt Γ);
                                          gen_nil (PropLeaf P);
                                          derives_to_gen_tree p
                                      ])
  | forallP_intro Γ P p => gen_cons 3 ([
                                          gen_nil (Ctxt Γ);
                                          gen_nil (PropLeaf P);
                                          derives_to_gen_tree p
                                      ])
  | imp_elim Γ P Q p q => gen_cons 4 ([
                                         gen_nil (Ctxt Γ);
                                         gen_nil (PropLeaf P);
                                         gen_nil (PropLeaf Q);
                                         derives_to_gen_tree p;
                                         derives_to_gen_tree q
                                     ])
  | forallt_elim Γ P t p => gen_cons 5 ([
                                           gen_nil (Ctxt Γ);
                                           gen_nil (PropLeaf P);
                                           gen_nil (Tm t);
                                           derives_to_gen_tree p
                                       ])
  | forallP_elim Γ P Q p => gen_cons 6 ([
                                           gen_nil (Ctxt Γ);
                                           gen_nil (PropLeaf P);
                                           gen_nil (Pred Q);
                                           derives_to_gen_tree p
                                       ])
  | compr_intro Γ P t p => gen_cons 7 ([
                                          gen_nil (Ctxt Γ);
                                          gen_nil (PropLeaf P);
                                          gen_nil (Tm t);
                                          derives_to_gen_tree p
                                      ])
  | compr_elim Γ P t p => gen_cons 8 ([
                                         gen_nil (Ctxt Γ);
                                         gen_nil (PropLeaf P);
                                         gen_nil (Tm t);
                                         derives_to_gen_tree p
                                     ])
  | zero_S Γ => gen_cons 9 ([gen_nil (Ctxt Γ)])
  | inj_S Γ => gen_cons 10 ([gen_nil (Ctxt Γ)])
  | plus_Z Γ => gen_cons 11 ([gen_nil (Ctxt Γ)])
  | plus_S Γ => gen_cons 12 ([gen_nil (Ctxt Γ)])
  | times_Z Γ => gen_cons 13 ([gen_nil (Ctxt Γ)])
  | times_S Γ => gen_cons 14 ([gen_nil (Ctxt Γ)])
  end.

Lemma eqdec_tm : forall (t u : tm), {t = u} + {t <> u}.
Proof.
  decide equality.
  decide equality.
Qed.

Lemma eqdec_prop : forall (p q : prop), {p = q} + {p <> q}
with eqdec_pred : forall (p q : pred),  {p = q} + {p <> q}.
Proof.
  repeat decide equality.
  repeat decide equality.
Qed.

Lemma eqdec_ctxt : forall (Γ Δ : ctxt), {Γ = Δ} + {Γ <> Δ}.
Proof.
  decide equality.
  apply eqdec_prop.
Qed.

Hint Resolve eqdec_prop eqdec_ctxt eqdec_pred.

Open Scope subst_scope.

Lemma nth_error_dec (Γ : ctxt) n P : { nth_error Γ n = Some P } + { nth_error Γ n <> Some P}.
Proof.
  destruct (nth_error Γ n) eqn:eq; [ | right; intro h; inversion h].
  destruct (eqdec_prop P p); [left | right].
  - subst; auto.
  - intro h; inversion h; subst; congruence.
Qed.

Require Import Coq.Logic.Eqdep_dec.


Check UIP_dec.

Lemma eqdec_refl : forall A (x : A) (p : { x = x } + { x <> x }), (forall (x y : A), {x = y} + {x <> y}) -> p = left Logic.eq_refl.
Proof.
  intros; destruct p.
  - f_equal; apply UIP_dec; auto.
  - congruence.
Qed.

Fixpoint gen_tree_to_derives (g : gen_tree derivation_leaf) Γ P : option (Γ ⊢ P).
  refine
    (match g with
     | gen_cons 0 ([
                      gen_nil (Loc n);
                      gen_nil (Ctxt Γ)
                  ]) => _
     | gen_cons 1 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      gen_nil (PropLeaf Q);
                      p
               ]) =>  _
     | gen_cons 2 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      p
                  ]) =>  _
     | gen_cons 3 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      p
                  ]) =>  _
     | gen_cons 4 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      gen_nil (PropLeaf Q);
                      p;
                      q
               ]) =>  _
     | gen_cons 5 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      gen_nil (Tm t);
                      p
                  ]) => _
     | gen_cons 6 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      gen_nil (Pred Q);
                      p
                  ]) =>  _
     | gen_cons 7 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      gen_nil (Tm t);
                      p
                  ]) =>  _
     | gen_cons 8 ([
                      gen_nil (Ctxt Γ);
                      gen_nil (PropLeaf P);
                      gen_nil (Tm t);
                      p
                  ]) =>  _
     | gen_cons 9 ([gen_nil (Ctxt Γ)]) => _
     | gen_cons 10 ([gen_nil (Ctxt Γ)]) => _
     | gen_cons 11 ([gen_nil (Ctxt Γ)]) => _
     | gen_cons 12 ([gen_nil (Ctxt Γ)]) => _
     | gen_cons 13 ([gen_nil (Ctxt Γ)]) => _
     | gen_cons 14 ([gen_nil (Ctxt Γ)]) => _
     | _ => None
     end).
  - destruct (nth_error_dec Γ n P); [| exact None].
    destruct (eqdec_ctxt Γ0 Γ);
      [ | exact None].
    apply Some; subst; eapply axiom.
    exact e.
  - destruct (gen_tree_to_derives p (P::Γ) Q); [| exact None].
    destruct (eqdec_ctxt Γ0  Γ); [ | exact None].
    destruct (eqdec_prop P0 (P ⇒ Q)); [ | exact None].
    subst.
    apply Some; apply imp_intro; exact d2.
  - destruct (gen_tree_to_derives p (lift_tm Γ) P); [ | exact None].
    destruct (eqdec_ctxt Γ0 Γ); [ | exact None].
    destruct (eqdec_prop P0 (all P)); [ | exact None].
    subst; apply Some; eapply forallt_intro; exact d1.
  - destruct (gen_tree_to_derives p (lift_prop Γ) P); [ | exact None].
    destruct (eqdec_ctxt Γ0 Γ); [ | exact None].
    destruct (eqdec_prop P0 (FORALL P)); [ | exact None].
    subst; apply Some; eapply forallP_intro; exact d1.
  - destruct (gen_tree_to_derives p Γ (P ⇒ Q)); [ | exact None].
    destruct (gen_tree_to_derives q Γ P); [ | exact None].
    destruct (eqdec_ctxt Γ0 Γ); [ | exact None].
    destruct (eqdec_prop P0 Q); [| exact None].
    subst; apply Some; eapply imp_elim; eauto.
  - destruct (gen_tree_to_derives p Γ (all P)); [ | exact None].
    destruct (eqdec_ctxt Γ0 Γ); [ | exact None].
    destruct (eqdec_prop P0 (P[t..;ids])); [ | exact None].
    subst.
    apply Some.
    apply forallt_elim.
    exact d2.
  - destruct (gen_tree_to_derives p Γ (FORALL P)); [ | exact None].
    destruct (eqdec_ctxt Γ0 Γ); [ | exact None].
    destruct (eqdec_prop P0 (P[ids;Q..])); [ | exact None].
    subst.
    apply Some.
    apply forallP_elim.
    exact d2.
  - destruct (gen_tree_to_derives p Γ P[t..;ids]); [| exact None].
    destruct (eqdec_ctxt Γ0 Γ); [ | exact None].
    destruct (eqdec_prop P0 (t ∈ {{ _ | P }})); [ | exact None].
    subst.
    apply Some; eapply compr_intro.
    exact d2.
  - destruct (gen_tree_to_derives p Γ (t ∈ {{_ | P}})); [|exact None].
    destruct (eqdec_ctxt Γ0 Γ); [| exact None].
    destruct (eqdec_prop P0 P[t..; ids]); [|exact None].
    subst; apply Some; eapply compr_elim.
    exact d2.
  - destruct (eqdec_ctxt Γ0 Γ); [|exact None].
    destruct (eqdec_prop P (all Succ (var_tm 0) ≄ Z)); [|exact None].
    subst; apply Some; apply zero_S.
  - destruct (eqdec_ctxt Γ0 Γ); [|exact None].
    destruct (eqdec_prop P (all all Succ (var_tm 1) ≃ Succ (var_tm 0) ⇒ var_tm 1 ≃ var_tm 0)); [|exact None].
    subst; apply Some; apply inj_S.
  - destruct (eqdec_ctxt Γ0 Γ); [|exact None].
    destruct (eqdec_prop P (all ha2_syn.Add (var_tm 0) Z ≃ var_tm 0)); [|exact None].
    subst; apply Some; apply plus_Z.
  - destruct (eqdec_ctxt Γ0 Γ); [|exact None].
    destruct (eqdec_prop P (all (all ha2_syn.Add (var_tm 1) (Succ (var_tm 0)) ≃ Succ (ha2_syn.Add (var_tm 1) (var_tm 0))))); [|exact None].
    subst; apply Some; apply plus_S.
  - destruct (eqdec_ctxt Γ0 Γ); [|exact None].
    destruct (eqdec_prop P (all Mult (var_tm 0) Z ≃ Z)); [|exact None].
    subst; apply Some; apply times_Z.
  - destruct (eqdec_ctxt Γ0 Γ); [|exact None].
    destruct (eqdec_prop P (all (all Mult (var_tm 1) (Succ (var_tm 0)) ≃ ha2_syn.Add (var_tm 1) (Mult (var_tm 1) (var_tm 0))))); [|exact None].
    subst; apply Some; apply times_S.
Defined.


Ltac elim_eqdec :=
  lazymatch goal with
  | [ |- context[eqdec_ctxt ?X ?X] ] =>
      assert (ee : eqdec_ctxt X X = left Logic.eq_refl) by (apply eqdec_refl; auto);
      rewrite ee; clear ee; unfold eq_rec_r; simpl; auto
  | [ |- context[eqdec_prop ?X ?X] ] =>
      assert (ee : eqdec_prop X X = left Logic.eq_refl) by (apply eqdec_refl; auto);
      rewrite ee; clear ee; unfold eq_rec_r; simpl; auto
  | [ |- context[eqdec_tm ?X ?X] ] =>
      assert (ee : eqdec_tm X X = left Logic.eq_refl) by (apply eqdec_refl; auto);
      rewrite ee; clear ee; unfold eq_rec_r; simpl; auto
  | _ => fail
  end.

Lemma is_retract_proof_to_gen_tree : forall Γ P (p : Γ ⊢ P),
    gen_tree_to_derives (derives_to_gen_tree p) Γ P = Some p.
Proof.
  induction p; try (simpl; try rewrite IHp; simpl; now repeat elim_eqdec).
  - simpl; destruct (nth_error_dec Γ n P).
    + elim_eqdec.
      f_equal; f_equal; auto.
      apply UIP_dec; decide equality.
    + subst; congruence.
  - simpl; rewrite IHp1, IHp2; simpl.
    repeat elim_eqdec.
Qed.

Print retract.

Instance retract_derives Γ P : retract (gen_tree derivation_leaf) (Γ ⊢ P).
Proof.
  refine {| in_A := derives_to_gen_tree; out_A g := gen_tree_to_derives g Γ P |}.
  apply is_retract_proof_to_gen_tree.
Defined.


Print derivation_leaf.

Print Instances has_depth.

Instance has_depth_derivation_leaf : has_depth derivation_leaf :=
  {|
    depth l :=
    match l with
    | Loc n => S n
    | Ctxt Γ => depth Γ
    | PropLeaf p => depth p
    | Pred p => depth p
    | Tm t => depth t
    end
  |}.

Print enum.

Instance enum_derivation_leaf : enum derivation_leaf.
Proof.
  refine
    {|
      list_up_to n :=
      let locs := map Loc (list_up_to n) in
      let ctxts := map Ctxt (list_up_to n) in
      let props := map PropLeaf (list_up_to n) in
      let preds := map Pred (list_up_to n) in
      let tms := map Tm (list_up_to n) in
      locs ++ ctxts ++ props ++ preds ++ tms
    |}.
  intros n a dpth; destruct a; simpl in dpth; repeat rewrite in_app_iff.
  - left.
    apply in_map.
    apply list_has_all; auto.
  - right; left.
    apply in_map; apply list_has_all; auto.
  - right; right; left.
    apply in_map; apply list_has_all; auto.
  - right; right; right; left;    
    apply in_map; apply list_has_all; auto.
  - right; right; right; right;
      apply in_map; apply list_has_all; auto.
Defined.

Instance has_depth_derives Γ P : has_depth (Γ ⊢ P).
Proof.
  Check @has_depth_iso.
  eapply @has_depth_iso.
  apply (_ : has_depth (gen_tree derivation_leaf)).
  apply retract_derives.
Defined.

Instance enum_derives Γ P : enum (Γ ⊢ P).
Proof.
  eapply @enum_iso.
  apply _.
Defined.


(* TODO: define proof bundles and enum them. *)

Record proof_bundle := { hyps : ctxt; concl : prop; proof : hyps ⊢ concl }.


Print countable.has_depth.

Instance has_depth_proof_bundle : has_depth proof_bundle :=
  {|
    depth b :=
    let '{| hyps := hyps; concl := concl; proof:= proof |} := b in
    depth hyps + depth concl + depth proof
  |}.

Print Instances enum.

Check concat_map.
Search (list (list _) -> _).

Definition concat_map {A B} (f : A -> list B) l :=
  concat (map f l).

Lemma in_concat_map : forall A B (f : A -> list B) l x,
    (exists y, In y l /\ In x (f y)) -> In x (concat_map f l).
Proof.
  intros.
  apply in_concat.
  destruct H as [y [in_y in_x]].
  exists (f y); split; auto.
  apply in_map; auto.
Qed.

Print enum.

Require Import Lia.

Instance enum_proof_bundle : enum proof_bundle.
Proof.
  refine
    {|
      list_up_to n :=
      let props : list prop := list_up_to n in
      let ctxts : list ctxt := list_up_to n in
      let pairs := list_prod props ctxts in
      concat_map (fun '(pair P Γ) =>
                    let prfs := list_up_to (A := Γ ⊢ P) n in
                    map (fun p => {| hyps := Γ; concl := P; proof := p |}) prfs)
                 pairs
    |}.
  intros n a dpth; destruct a.
  apply in_concat_map.
  assert (dpth_concl : depth concl0 <= n) by (simpl in dpth; simpl; lia).
  assert (dpth_hyps : depth hyps0 <= n) by (simpl in dpth; simpl; lia).
  assert (dpth_proof : depth proof0 <= n) by (simpl in dpth; simpl; lia).
  clear dpth.
  exists (pair concl0 hyps0); split.
  - apply in_prod; apply list_has_all; auto.
  - apply in_map.
    apply list_has_all; auto.
Defined.

Locate "∃".


Definition lower : fin -> fin := Nat.pred.

Definition lower_prop (P : prop) := P⟨id; lower⟩.
Lemma lower_lift_prop : forall P, lower_prop (P⟨id; ↑⟩) = P.
Proof.
  intros; unfold lower_prop; asimpl.
  erewrite extRen_prop.
  - rewrite rinstId_prop.
    reflexivity.
  - auto.
  - auto.
Qed.

Locate "∃".

Print sig.

Definition exists_dec (P : prop) : option {Q | P = ∃ Q}.
  refine
    (match P with
     | (FORALL (all Q ⇒ all var_tm 0 ∈ var_pred 0) ⇒ all var_tm 0 ∈ var_pred 0) =>
         if eqdec_prop ((lower_prop Q)⟨id; ↑⟩) Q then
           Datatypes.Some (exist _ (lower_prop Q) _)
         else None
     | _ => Datatypes.None
     end).
  rewrite e; auto.
Defined.

Require Import ConstructiveEpsilon.
Section extract.

  Parameter is_dec : prop -> bool.

  Definition ex_val P n := eval_prop bot_pval (n, bot_vval) P.
  
  Hypothesis is_dec_correct :
    forall P,
      is_dec P ->
              forall n, { ex_val P n } + { ~ ex_val P n }.

  Definition num_of_proof Γ P (p : Γ ⊢ P) : nat.
    destruct Γ; [ |  exact 0].
    destruct (exists_dec P) as [ [Q h] | ]; [|exact 0].
    destruct (Sumbool.sumbool_of_bool (is_dec Q)) as [dec |]; [| exact 0].
    eapply constructive_ground_epsilon_nat.
    - apply is_dec_correct; apply dec.
    - apply ex_refl.
      subst; auto.
  Defined.

  Print num_of_proof.

  Theorem num_of_proof_correct : forall P (p : nil ⊢ ∃ P),
      is_dec P ->
      ex_val P (num_of_proof nil (∃ P) p).
  Proof.
    intros; simpl.
    rewrite lower_lift_prop.
    elim_eqdec.
    destruct (Sumbool.sumbool_of_bool (is_dec P)); [ | congruence].
    (* No need to check anything here, it's all in the term! *)
    apply constructive_ground_epsilon_spec_nat.
  Qed.

  Definition num_of_all_proofs n : nat :=
    let proofs : list proof_bundle := list_up_to n in
    let nums := map (fun '{| hyps := hyps; concl := concl; proof := proof |} =>
                       num_of_proof hyps concl proof)
                    proofs
    in
    list_max nums.

  Lemma list_max_ge : forall l m,
      (exists n, In n l /\ m <= n) -> m <= list_max l.
  Proof.
    intros l m [n [in_n m_le_n]].
    induction l; simpl.
    - destruct in_n.
    - simpl in in_n.
      destruct in_n.
      + subst.
        lia.
      + assert (h := IHl H).
        lia.
  Qed.
    
  Print has_depth_proof_bundle.
  Eval compute in depth nil.

  Theorem num_of_all_proofs_lt : forall m P (p : nil ⊢ (∃ P)),
      is_dec P ->
      (forall n, ex_val P n -> m <= n) ->
      m <= num_of_all_proofs ((depth (∃ P)) + (depth p)).
  Proof.
    intros m P p dec ex.
    unfold num_of_all_proofs.
    apply list_max_ge.
    exists (num_of_proof nil (∃ P) p).
    split; [ | apply ex; apply num_of_proof_correct; now auto].
    Search (In _ (list_map _ _)).
    apply in_map_iff.
    exists {| hyps := nil; concl := (∃ P); proof := p |}.
    split; [ now auto |].
    apply list_has_all.
    reflexivity.
Qed.  

End extract.
