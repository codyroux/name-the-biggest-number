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


Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).

Inductive type :=
| tpNat: type
| tpArr: type -> type -> type.

Fixpoint type_eqb(t1 t2: type): bool :=
  match t1, t2 with
  | tpNat, tpNat => true
  | tpArr A B, tpArr C D => andb (type_eqb A C) (type_eqb B D)
  | _, _ => false
  end.

Fixpoint interp_type(tp: type): Type :=
  match tp with
  | tpNat => nat
  | tpArr t1 t2 => (interp_type t1) -> (interp_type t2)
  end.

Require Import List String.

Inductive term :=
| tVar(x: string)
| tLam(x: string)(A B: type)(body: term)
| tApp(t1 t2: term)
| tO
| tS
| tNatRec(R: type).

Definition lookup{T}(e: list (string * T))(x: string): option T :=
  'Some (_, t) <- List.find (fun '(y, t) => String.eqb x y) e; Some t.

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

Definition interp_term: forall (e: list (string * {tp: type & interp_type tp})) (t: term),
    {tp: type & interp_type tp}.
  refine (fix rec e t {struct t} :=
  match t with
  | tVar x => _
  | tLam x A B body => _
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
    set (r := (projT2 (rec ((x, (existT _ A x')) :: e) body))).
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

Lemma interp_tVar_head: forall e x (p: {tp: type & interp_type tp}),
    interp_term ((x, p) :: e) (tVar x) = p.
Proof.
  intros. simpl. unfold lookup, List.find.
  rewrite String.eqb_refl. reflexivity.
Qed.

Lemma interp_tVar_tail: forall e x y (p1 p2: {tp: type & interp_type tp}),
    String.eqb y x = false ->
    interp_term e (tVar y) = p2 ->
    interp_term ((x, p1) :: e) (tVar y) = p2.
Proof.
  intros. simpl. unfold lookup, List.find.
  rewrite H. rewrite <- H0. reflexivity.
Qed.

Lemma interp_tLam: forall e x A B body f,
  (forall x0, interp_term ((x, existT interp_type A x0) :: e) body = existT _ B (f x0)) ->
  interp_term e (tLam x A B body) = existT _ (tpArr A B) f.
Proof.
  simpl.
  intros.
  f_equal.
  extensionality x'.
  specialize (H x').
  destruct (interp_term ((x, existT interp_type A x') :: e) body) eqn: E.
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

Lemma ack'_reification_helper: exists res,
    interp_term nil res
    = existT _ (tpArr tpNat (tpArr tpNat (tpArr tpNat tpNat))) ack'.
Proof.
  eexists.
  unfold ack'.

  repeat lazymatch goal with
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
    first [eapply interp_tVar_head | eapply interp_tVar_tail]
  end.

Abort.


Definition contender_5: nat. Admitted.


Theorem contender_4_lt_contender_5 : contender_4 < contender_5.
Proof.
Admitted.
