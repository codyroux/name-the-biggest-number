Require Import Arith Lia.


Fixpoint iter (f : nat -> nat) (b : nat) :=
  match b with
  | 0 => 1
  | S b' => f (iter f b')
  end.

Fixpoint ack (n a b : nat) :=
  match n with
  | 0 => S b
  | 1 => a + b
  | S n' => iter (ack n' a) b
  end.


(* This is the previous contender for largest number *)
(* Submitted by codyroux *)
Definition contender_4 := ack 5 42 10002.


Require Import List. Import ListNotations.


(* Definition of the language STLC+NatRec: *)

Inductive type :=
| tpNat: type
| tpArr: type -> type -> type.

Fixpoint type_eqb(t1 t2: type): bool :=
  match t1, t2 with
  | tpNat, tpNat => true
  | tpArr A B, tpArr C D => andb (type_eqb A C) (type_eqb B D)
  | _, _ => false
  end.

Fixpoint type_size(t: type): nat :=
  match t with
  | tpNat => 1
  | tpArr t1 t2 => S (type_size t1 + type_size t2)
  end.

Fixpoint interp_type(tp: type): Type :=
  match tp with
  | tpNat => nat
  | tpArr t1 t2 => (interp_type t1) -> (interp_type t2)
  end.

Inductive term :=
| tVar(x: nat) (* 0 = last element of the env, ie the outermost binder (reversed DeBruijn) *)
| tLam(A B: type)(body: term)
| tApp(t1 t2: term)
| tO
| tS
| tNatRec(R: type).

Definition nat_size(n: nat) := S n.

Fixpoint term_size(t: term): nat :=
  match t with
  | tVar x => S (nat_size x)
  | tLam A B body => S (type_size A + type_size B + term_size body)
  | tApp t1 t2 => S (term_size t1 + term_size t2)
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_size R)
  end.

Definition lookup{T}(e: list T)(n: nat): option T :=
  let l := List.length e in if l <=? n then None else nth_error e (l - S n).

Goal lookup [10; 11; 12] 0 = Some 12. reflexivity. Qed.
Goal lookup [10; 11; 12] 1 = Some 11. reflexivity. Qed.
Goal lookup [10; 11; 12] 2 = Some 10. reflexivity. Qed.
Goal lookup [10; 11; 12] 3 = None. reflexivity. Qed.

Definition error{tp: type}: interp_type tp.
  revert tp.
  refine (fix rec tp := _).
  destruct tp; simpl.
  - exact 42.
  - intros _. apply rec.
Defined.

Definition cast_error(from to: type):
  ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)).
  split; intros; exact error.
Qed.

Definition cast_impl(from to: type):
  ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)).
  revert from to.
  induction from; intros; simpl in *.
  - destruct to; simpl.
    + split; exact id.
    + exact (cast_error tpNat (tpArr to1 to2)).
  - destruct to.
    + exact (cast_error (tpArr from1 from2) tpNat).
    + destruct (type_eqb from1 to1) eqn: E1;
      destruct (type_eqb from2 to2) eqn: E2;
      simpl in *.
      {
        specialize (IHfrom1 to1).
        specialize (IHfrom2 to2).
        destruct IHfrom1 as [F1T1 T1F1].
        destruct IHfrom2 as [F2T2 T2F2].
        split.
        * intros F arg. apply F2T2. apply F. apply T1F1. apply arg.
        * intros F arg. apply T2F2. apply F. apply F1T1. apply arg.
      }
      all: exact (cast_error (tpArr from1 from2) (tpArr to1 to2)).
Defined.

(* designed to be computable (no opaque proofs) *)
Definition cast{from: type}(to: type): interp_type from -> interp_type to :=
  fst (cast_impl from to).

Definition interp_term: forall (e: list {tp: type & interp_type tp}) (t: term),
    {tp: type & interp_type tp}.
  refine (fix rec e t {struct t} :=
  match t with
  | tVar x => _
  | tLam A B body => _
  | tApp t1 t2 => _
  | tO => _
  | tS => _
  | tNatRec R => _
  end).
  - destruct (lookup e x) as [R|].
    + exact R.
    + exact (existT _ tpNat error).
  - refine (existT _ (tpArr A B) _).
    simpl.
    intro x'.
    set (r := (projT2 (rec ((existT _ A x') :: e) body))).
    simpl in r.
    exact (cast B r).
  - destruct (rec e t1) as [R1 r1] eqn: E1.
    destruct (rec e t2) as [R2 r2] eqn: E2.
    destruct R1 as [|A B]; [exact (existT _ tpNat error)|].
    simpl in *.
    exact (existT _ _ (r1 (cast A r2))).
  - exact (existT _ tpNat 0).
  - exact (existT _ (tpArr tpNat tpNat) S).
  - set (r := (@Nat.recursion (interp_type R))).
    exact (existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R))) r).
Defined.


(* Defining the new contender: *)

Fixpoint typesUpTo(n: nat): list type :=
  match n with
  | O => []
  | S m =>
    let r := typesUpTo m in
    tpNat :: List.map (fun '(t1, t2) => tpArr t1 t2) (list_prod r r)
  end.

Lemma typesUpTo_correct: forall n t,
    type_size t <= n ->
    List.In t (typesUpTo n).
Proof.
  induction n; intros.
  - destruct t; simpl in *; lia.
  - simpl. destruct t; [auto|].
    right. simpl in *.
    match goal with
    | |- In ?e (map ?f _) => change e with (f (t1, t2))
    end.
    apply in_map.
    apply in_prod; eapply IHn; lia.
Qed.

Fixpoint natsUpTo(n: nat): list nat :=
  match n with
  | O => []
  | S m => m :: natsUpTo m
  end.

Lemma natsUpTo_correct: forall n m,
    nat_size m <= n ->
    List.In m (natsUpTo n).
Proof.
  induction n; intros; unfold nat_size in *.
  - exfalso. lia.
  - simpl. assert (n = m \/ S m <= n) as C by lia. destruct C as [C | C]; auto.
Qed.

Fixpoint termsUpTo(n: nat): list term :=
  match n with
  | O => []
  | S m =>
    List.map tVar (natsUpTo m) ++
    List.map (fun '(A, B, body) => tLam A B body)
             (list_prod (list_prod (typesUpTo m) (typesUpTo m)) (termsUpTo m)) ++
    List.map (fun '(t1, t2) => tApp t1 t2)
             (list_prod (termsUpTo m) (termsUpTo m)) ++
    [tO] ++ [tS] ++
    List.map tNatRec (typesUpTo m)
  end.

Lemma termsUpTo_correct: forall n t,
    term_size t <= n ->
    List.In t (termsUpTo n).
Proof.
  induction n; intros.
  - destruct t; simpl in *; lia.
  - destruct t; simpl in *.
    + do 0 (apply in_or_app; right). apply in_or_app; left.
      apply in_map. apply natsUpTo_correct. lia.
    + do 1 (apply in_or_app; right). apply in_or_app; left.
      match goal with
      | |- In ?e (map ?f _) => change e with (f (A, B, t))
      end.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply natsUpTo_correct
             | apply typesUpTo_correct
             | apply IHn
             | lia].
    + do 2 (apply in_or_app; right). apply in_or_app; left.
      match goal with
      | |- In ?e (map ?f _) => change e with (f (t1, t2))
      end.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply natsUpTo_correct
             | apply typesUpTo_correct
             | apply IHn
             | lia].
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. right. right.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply natsUpTo_correct
             | apply typesUpTo_correct
             | apply IHn
             | lia].
Qed.

Definition eval(t : term): nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return (interp_type t0 -> nat) with
  | tpNat         => fun (res: interp_type tpNat) => res
  | tpArr tp1 tp2 => fun (res: interp_type (tpArr tp1 tp2)) => 0
  end res.

Fixpoint listmax_impl(currentMax: nat)(l: list nat): nat :=
  match l with
  | nil => currentMax
  | cons h t => listmax_impl (max h currentMax) t
  end.

Definition listmax: list nat -> nat := listmax_impl 0.

Definition largest_STLCNatRec_nat_of_size(n: nat): nat :=
  listmax (List.map eval (termsUpTo n)).

Definition contender_5: nat := largest_STLCNatRec_nat_of_size 222.


(* Reification automation: *)

Definition type_eq_dec: forall x y : type, {x = y} + {x <> y}.
  induction x; destruct y eqn: E; intros; simpl.
  - left. reflexivity.
  - right. intro C. discriminate.
  - right. intro C. discriminate.
  - specialize (IHx1 t1).
    specialize (IHx2 t2).
    destruct IHx1 as [E1 | N1]; destruct IHx2 as [E2 | N2]; try (right; congruence).
    left. subst. reflexivity.
Defined.

Lemma type_eqb_true: forall t1 t2, type_eqb t1 t2 = true -> t1 = t2.
Proof.
  induction t1; intros; destruct t2; simpl in *; try congruence.
  apply Bool.andb_true_iff in H. destruct H. f_equal; eauto.
Qed.

Lemma type_eqb_same: forall t, type_eqb t t = true.
Proof.
  induction t; simpl.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(* only for the reification machinery, will not show up in the final proof *)
Require Import FunctionalExtensionality.

Lemma cast_impl_same: forall (B: type) (t: interp_type B),
    fst (cast_impl B B) t = t /\ snd (cast_impl B B) t = t.
Proof.
  induction B; intros; simpl; unfold id.
  - auto.
  - do 2 rewrite type_eqb_same.
    destruct (cast_impl B1 B1) as [fw1 bw1] eqn: E1.
    destruct (cast_impl B2 B2) as [fw2 bw2] eqn: E2.
    simpl in *.
    split; extensionality arg.
    + specialize (IHB1 arg).
      apply proj2 in IHB1.
      rewrite IHB1.
      specialize (IHB2 (t arg)).
      apply proj1 in IHB2.
      exact IHB2.
    + specialize (IHB1 arg).
      apply proj1 in IHB1.
      rewrite IHB1.
      specialize (IHB2 (t arg)).
      apply proj2 in IHB2.
      exact IHB2.
Qed.

Lemma cast_same: forall (B: type) (t: interp_type B),
    cast B t = t.
Proof.
  intros. unfold cast.
  pose proof (cast_impl_same B t) as P.
  apply proj1 in P.
  exact P.
Qed.

Lemma interp_tVar: forall e x (p: {tp: type & interp_type tp}),
    lookup e x = Some p ->
    interp_term e (tVar x) = p.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma interp_tVar_head: forall e y (p: {tp: type & interp_type tp}),
    y = List.length e ->
    interp_term (p :: e) (tVar y) = p.
Proof.
  intros. subst. simpl. unfold lookup, List.find.
  change (length (p :: e)) with (S (length e)).
  destruct (S (length e) <=? length e) eqn: E. {
    apply Nat.leb_le in E. exfalso. lia.
  }
  rewrite Nat.sub_diag.
  reflexivity.
Qed.

Lemma interp_tVar_tail: forall e y (p1 p2: {tp: type & interp_type tp}),
    length e <=? y = false ->
    interp_term e (tVar y) = p2 ->
    interp_term (p1 :: e) (tVar y) = p2.
Proof.
  intros. simpl in *. unfold lookup, List.find in *.
  change (length (p1 :: e)) with (S (length e)).
  rewrite H in H0.
  apply Nat.leb_gt in H.
  replace (S (length e) - S y) with (S (length e - S y)) by lia.
  destruct (S (length e) <=? y) eqn: E. {
    apply Nat.leb_le in E. exfalso. lia.
  }
  simpl.
  assumption.
Qed.

Lemma interp_tLam: forall e A B body f,
  (forall x0, interp_term (existT interp_type A x0 :: e) body = existT _ B (f x0)) ->
  interp_term e (tLam A B body) = existT _ (tpArr A B) f.
Proof.
  simpl.
  intros.
  f_equal.
  extensionality x'.
  specialize (H x').
  destruct (interp_term (existT interp_type A x' :: e) body) eqn: E.
  inversion H.
  subst.
  simpl.
  apply cast_same.
Qed.

Lemma interp_tApp: forall e t1 t2 A B (f: interp_type A -> interp_type B) (a: interp_type A),
    interp_term e t1 = existT _ (tpArr A B) f ->
    interp_term e t2 = existT _ A a ->
    interp_term e (tApp t1 t2) = existT _ B (f a).
Proof.
  intros.
  simpl.
  destruct (interp_term e t1) eqn: E1.
  destruct (interp_term e t2) eqn: E2.
  pose proof (EqdepFacts.eq_sigT_fst H). subst x.
  apply Eqdep_dec.inj_pair2_eq_dec in H. 2: apply type_eq_dec. subst i.
  pose proof (EqdepFacts.eq_sigT_fst H0). subst x0.
  apply Eqdep_dec.inj_pair2_eq_dec in H0. 2: apply type_eq_dec. subst i0.
  rewrite cast_same.
  reflexivity.
Qed.

Lemma interp_tO: forall e, interp_term e tO = existT _ tpNat 0.
Proof. intros. reflexivity. Qed.

Lemma interp_tS: forall e, interp_term e tS = existT _ (tpArr tpNat tpNat) S.
Proof. intros. reflexivity. Qed.

Lemma interp_tNatRec: forall e R,
    interp_term e (tNatRec R) =
    existT _ (tpArr R (tpArr (tpArr tpNat (tpArr R R)) (tpArr tpNat R)))
           (@Nat.recursion (interp_type R)).
Proof.
  intros. subst. reflexivity.
Qed.

(*
Notation "A --> B" := (tpArr A B) (at level 60, right associativity).
*)

Ltac reify_type T :=
  lazymatch T with
  | ?A -> ?B => let A' := reify_type A in
                let B' := reify_type B in
                constr:(tpArr A' B')
  | nat => constr:(tpNat)
  | interp_type ?A => constr:(A)
  | _ => fail "" T "is not a type"
  end.

Ltac t :=
  lazymatch goal with
  | |- interp_term ?e ?t = existT _ ?T (fun _ => _) =>
    eapply interp_tLam; intros ?
  | |- interp_term ?e ?t = existT _ ?T O =>
    eapply interp_tO
  | |- interp_term ?e ?t = existT _ ?T S =>
    eapply interp_tS
  | |- interp_term ?e ?t = existT _ ?T Nat.recursion =>
    eapply interp_tNatRec
  | |- interp_term ?e ?t = existT _ ?B (?f ?a) =>
    let A := type of a in
    let A := eval cbv beta iota in A in
    let A := reify_type A in
    eapply (interp_tApp e _ _ A B)
  | |- interp_term ?e ?t = existT _ ?T ?x =>
    is_var x;
    first [ eapply interp_tVar_head; cbv [length]; reflexivity
          | eapply interp_tVar_tail; cbv [length]]
  end.


(* Expressing contender_4 as an STLC+NatRec term: *)

Definition ack'(n: nat): nat -> nat -> nat :=
  Nat.recursion
    (fun a b => S b)
    (fun (pred0: nat) (rec0: nat -> nat -> nat) =>
       Nat.recursion
         (Nat.recursion (fun (m: nat) => m)
                        (fun (pred: nat) (rec: nat -> nat) (m: nat) => S (rec m)))
         (fun (pred: nat) (rec: nat -> nat -> nat) =>
            (fun a b => Nat.recursion 1 (fun pred1 rec1 => rec a rec1) b))
         pred0)
    n.

Lemma iter_proper: forall f1 f2,
    (forall x, f1 x = f2 x) ->
    forall b, iter f1 b = iter f2 b.
Proof.
  induction b.
  - reflexivity.
  - simpl. rewrite IHb. apply H.
Qed.

Definition iter' (f : nat -> nat) : nat -> nat :=
  Nat.recursion 1 (fun (pred: nat) (rec: nat) => f rec).

Lemma iter'_equiv: forall f b, iter' f b = iter f b.
Proof. induction b; intros; simpl; congruence. Qed.

Definition add': nat -> nat -> nat :=
  Nat.recursion (fun (m: nat) => m) (fun (pred: nat) (rec: nat -> nat) (m: nat) => S (rec m)).

Lemma add'_equiv: forall n m, add' n m = Nat.add n m.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite <- IHn. reflexivity.
Qed.

Lemma ack'_equiv: forall n a b, ack' n a b = ack n a b.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - destruct n.
    + simpl. apply add'_equiv.
    + specialize (IHn a).
      rewrite <- (iter_proper _ _ IHn).
      rewrite <- iter'_equiv. reflexivity.
Qed.

Lemma ack'_reification_helper: exists res,
    interp_term nil res
    = existT _ (tpArr tpNat (tpArr tpNat (tpArr tpNat tpNat))) ack'.
Proof.
  eexists.
  unfold ack'.
  repeat t.
  all: reflexivity.
Defined.

Definition ack_reified: term.
  let r := eval unfold ack'_reification_helper in ack'_reification_helper in
  match r with
  | ex_intro _ ?x _ => exact x
  end.
Defined.

Lemma interp_ack_reified: projT2 (interp_term nil ack_reified) = ack'.
Proof. reflexivity. Qed.

Eval cbv in (term_size ack_reified).

(* Proving that the new contender is bigger than the previous one: *)

Theorem contender_4_lt_contender_5 : contender_4 < contender_5.
Proof.
Admitted.
