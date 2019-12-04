Require Import Arith Lia.
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

Fixpoint type_depth(t: type): nat :=
  match t with
  | tpNat => 1
  | tpArr t1 t2 => S (max (type_depth t1) (type_depth t2))
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

Definition nat_depth(n: nat) := S n.

Fixpoint term_depth(t: term): nat :=
  match t with
  | tVar x => S (nat_depth x)
  | tLam A B body => S (max (max (type_depth A) (type_depth B)) (term_depth body))
  | tApp t1 t2 => S (max (term_depth t1) (term_depth t2))
  | tO => 1
  | tS => 1
  | tNatRec R => S (type_depth R)
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
  - exact 0.
  - intros _. apply rec.
Defined.

Definition cast_error(from to: type):
  ((interp_type from -> interp_type to) * (interp_type to -> interp_type from)).
  split; intros; exact error.
Defined.

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
    type_depth t <= n <-> List.In t (typesUpTo n).
Proof.
  induction n; intros; split; intros.
  - destruct t; simpl in *; lia.
  - simpl in *. contradiction.
  - simpl. destruct t; [auto|].
    right. simpl in *.
    match goal with
    | |- In ?e (map ?f _) => change e with (f (t1, t2))
    end.
    apply in_map.
    apply in_prod; eapply IHn; lia.
  - simpl in *. destruct H.
    + subst. simpl. lia.
    + apply in_map_iff in H.
      destruct H as [[t1 t2] [? H]].
      subst t.
      apply in_prod_iff in H.
      destruct H as [H1 H2].
      pose proof ((proj2 (IHn _)) H1).
      pose proof ((proj2 (IHn _)) H2).
      simpl.
      lia.
Qed.

Fixpoint natsUpTo(n: nat): list nat :=
  match n with
  | O => []
  | S m => m :: natsUpTo m
  end.

Lemma natsUpTo_correct: forall n m,
    nat_depth m <= n <-> List.In m (natsUpTo n).
Proof.
  induction n; intros; unfold nat_depth in *; split; intros; simpl in *.
  - exfalso. lia.
  - contradiction.
  - assert (n = m \/ S m <= n) as C by lia. destruct C as [C | C]; firstorder idtac.
  - destruct H.
    + lia.
    + specialize (IHn m). apply proj2 in IHn. specialize (IHn H). lia.
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
    term_depth t <= n <-> List.In t (termsUpTo n).
Proof.
  induction n; intros; split; intros.
  - destruct t; simpl in *; lia.
  - simpl in *. contradiction.
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
             | apply (proj1 (natsUpTo_correct _ _))
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia].
    + do 2 (apply in_or_app; right). apply in_or_app; left.
      match goal with
      | |- In ?e (map ?f _) => change e with (f (t1, t2))
      end.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (natsUpTo_correct _ _))
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia].
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. auto.
    + do 3 (apply in_or_app; right). simpl. right. right.
      repeat first
             [ apply in_map
             | apply in_prod
             | apply (proj1 (natsUpTo_correct _ _))
             | apply (proj1 (typesUpTo_correct _ _))
             | apply (proj1 (IHn _))
             | lia].
  - simpl in *.
    repeat ((simpl in H || apply in_app_iff in H || idtac); destruct H).
    + apply in_map_iff in H.
      destruct H as [x [? H]].
      subst t.
      pose proof ((proj2 (natsUpTo_correct _ _)) H).
      simpl.
      lia.
    + apply in_map_iff in H.
      destruct H as [[[A B] body] [? H]].
      subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      pose proof ((proj2 (typesUpTo_correct _ _)) H1).
      pose proof ((proj2 (IHn _)) H0).
      simpl.
      lia.
    + apply in_map_iff in H.
      destruct H as [[t1 t2] [? H]].
      subst t.
      repeat (apply in_prod_iff in H; destruct H).
      pose proof ((proj2 (IHn _)) H).
      pose proof ((proj2 (IHn _)) H0).
      simpl.
      lia.
    + simpl. lia.
    + simpl. lia.
    + apply in_map_iff in H.
      destruct H as [R [? H]].
      subst t.
      pose proof ((proj2 (typesUpTo_correct _ _)) H).
      simpl.
      lia.
Qed.

Definition eval(t : term): nat :=
  let (tp, res) := interp_term nil t in
  match tp as t0 return (interp_type t0 -> nat) with
  | tpNat         => fun (res: interp_type tpNat) => res
  | tpArr tp1 tp2 => fun (res: interp_type (tpArr tp1 tp2)) => 0
  end res.

Fixpoint maxBy{T: Type}(f: T -> nat)(currentMax: nat)(currentBest: T)(l: list T): T :=
  match l with
  | nil => currentBest
  | cons h t =>
    if currentMax <? (f h) then
      maxBy f (f h) h t
    else
      maxBy f currentMax currentBest t
  end.

Definition largest_of_depth(n: nat): term := maxBy eval 0 tO (termsUpTo n).

Eval vm_compute in (largest_of_depth 1).
Eval vm_compute in (largest_of_depth 2).
Eval vm_compute in (largest_of_depth 3).
Eval vm_compute in (largest_of_depth 4).

Definition largest_STLCNatRec_nat_of_depth(n: nat): nat := eval (largest_of_depth n).

(* Small examples are computable: *)
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 1).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 2).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 3).
Eval vm_compute in (largest_STLCNatRec_nat_of_depth 4).
(* but as soon as it would get interesting, it becomes too inefficient *)


(* This is the current contender for largest number *)
(* Submitted by samuelgruetter *)
(* <brag>Note how its definition does not require any large literals</brag> ;-) *)
Definition contender_5: nat := largest_STLCNatRec_nat_of_depth 42.

Require Hurkens.

Module TypeNequivSmallType.
Import Hurkens.

Section Paradox.

(* I feel like this version of the paradox should already by in
   Hurkens.v but can't find it, there's only the version with A=U *)

Definition U := Type.
Variable A:U.

Variable down : U -> A.
Variable up : A -> U.
Hypothesis up_down : forall (X:U), up (down X) = X.

Theorem paradox : False.
Proof.
  Generic.paradox p.
  (** Large universe *)
  + exact U.
  + exact (fun X=>X).
  + cbn. exact (fun X F => forall x:X, F x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + exact (fun F => forall x:A, F (up x)).
  + cbn. exact (fun _ f => fun x:A => f (up x)).
  + cbn. intros * f X.
    specialize (f (down X)).
    rewrite up_down in f.
    exact f.
  (** Small universe *)
  + exact A.
  (** The interpretation of [A] as a universe is [U]. *)
  + cbn. exact up.
  + cbn. exact (fun _ F => down (forall x, up (F x))).
  + cbn. exact (fun _ F => down (forall x, up (F x))).
  + cbn. exact (down False).
  + rewrite up_down in p.
    exact p.
  + cbn. easy.
  + cbn. intros ? f X.
    destruct (up_down X). cbn.
    reflexivity.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
Qed.

End Paradox.

End TypeNequivSmallType.

Inductive foo (A:Type) := bar X : foo X -> foo A | nonempty.
Arguments nonempty {_}.

Notation U := TypeNequivSmallType.U.

Definition A : U := foo nat.

Definition down : U -> A := fun u => bar nat u nonempty.

Definition up : A -> U := fun a => match a with bar _ u _ => u | nonempty => nat end.

Lemma up_down : forall (X:U), up (down X) = X.
Proof.
  reflexivity.
Qed.

Definition contender_final : nat := 7.

Lemma n_lt_contender_final :
  forall n, n < contender_final.
Proof (match TypeNequivSmallType.paradox A down up up_down with end).

Lemma contender_5_lt_contender_final : contender_5 < contender_final.
Proof.
  apply n_lt_contender_final.
Qed.

Print Assumptions contender_5_lt_contender_final.
