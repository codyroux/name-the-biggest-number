Require Import Arith Lia.


(* This is a fun trick *)
Opaque Nat.pow.

Definition tower_of_power (n : nat) : nat :=
  Nat.recursion 42 (fun _ k => 42 ^ k) n.

(* This is the previous contender for largest number *)
(* Submitted by codyroux *)
Definition contender_3 := tower_of_power 10000.

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


(* This is the current contender for largest number *)
(* Submitted by codyroux *)
Definition contender_4 := ack 5 42 10002.


Lemma ack_0 : forall a b, ack 0 a b = S b.
Proof.
  intros; reflexivity.
Qed.

Lemma ack_1 : forall a b, ack 1 a b = a + b.
Proof.
  intros; simpl.
  reflexivity.
Qed.

Lemma ack_2 : forall a b, ack 2 a b = a * b + 1.
Proof.
  intros a b. revert a; induction b; intros; simpl.
  - lia.
  - simpl in IHb.
    rewrite IHb.
    lia.
Qed.

Lemma ack_3_aux : forall b a, a ^ b = iter (fun k => a * k) b.
Proof.
  induction b; intros; simpl.
  - reflexivity.
  - rewrite <- IHb.
    auto.
Qed.

Definition ge_fun (f g : nat -> nat) :=
  forall n, f n <= g n.

Definition mon (f : nat -> nat) := forall n m, n <= m -> f n <= f m.

Definition geS (f : nat -> nat) := forall n, S n <= f n.


Lemma iter_ge_fun : forall f g b,
    ge_fun f g -> mon f -> iter f b <= iter g b.
Proof.
  intros; induction b; simpl; auto.
  transitivity (f (iter g b)); auto.
Qed.


Lemma ack_3 : forall a b, a ^ b <= ack 3 a b.
Proof.
  intros; rewrite ack_3_aux.
  apply iter_ge_fun.
  - intro n.
    induction n; try lia.
    simpl.
    replace (a * S n) with (a + (a * n)) by ring.
    lia.
  - intros n m; nia.
Qed.


Lemma unfold_iter : forall f b, iter f (S b) = f (iter f b).
Proof. reflexivity. Qed.

Lemma unfold_ack : forall n a b,
    2 <= n ->
    ack (S n) a b = iter (ack n a) b.
Proof.
  intros.
  case n as [|n]; [lia|].
  case n as [|n]; [lia|].
  reflexivity.
Qed.

Lemma ack_4_aux : forall b, tower_of_power b =
                            iter (fun k => 42 ^ k) (S b).
Proof.
  induction b.
  - reflexivity.
  - simpl.
    rewrite IHb.
    simpl.
    reflexivity.
Qed.

Lemma ack_4 : forall b, tower_of_power b <= ack 4 42 (S b).
Proof.
  intros.
  rewrite ack_4_aux.
  rewrite unfold_ack; [|lia].
  apply iter_ge_fun.
  - intro n.
    apply ack_3.
  - intros n m le.
    induction le; auto.
    replace (42 ^ (S m)) with (42 * (42 ^ m)) by reflexivity.
    nia.
Qed.


Lemma mon_ge_iter : forall f,
    mon f ->
    geS f ->
    f 0 <= 1 ->
    forall b, f b <= iter f b.
Proof.
  intros f mon_f ge_f.
  induction b; intros; simpl; [now auto|].
  apply mon_f.
  transitivity (f b); [apply ge_f | auto].
Qed.

Lemma mon_iter : forall f,
    mon f ->
    geS f ->
    f 0 <= 1 ->
    mon (iter f).
Proof.
  intros f mon_f geS_f f_0.
  intros n m le.
  induction le; [now auto|].
  simpl.
  transitivity (S (iter f m)); now auto.
Qed.
  

Lemma geS_ack : forall n a, 2 <= a -> geS (ack n a).
Proof.
  induction n; intros.
  - intro; simpl; lia.
  - intro b.
    case n as [|n]; [simpl; lia|].
    induction b; [simpl; now auto|].
    case n as [|n].
    + rewrite ack_2.
      nia.
    +
      rewrite unfold_ack; [|lia].
      rewrite unfold_iter.
      transitivity (S (ack (3 + n) a b)).
      -- apply le_n_S.
         apply IHb.
      -- apply IHn.
         auto.
Qed.
    
  
Lemma mon_ack_in_b : forall n a,
    2 <= a ->
    mon (fun b => ack n a b).
Proof.
  induction n; intros.
  - simpl; intros b m; lia.
  - simpl.
    intros b m le.
    case n as [|n]; [lia|].
    induction le; auto.
    rewrite unfold_iter.
    transitivity (S (iter (ack (S n) a) m)).
    + lia.
    + apply geS_ack; auto.
Qed.

Theorem contender_3_lt_contender_4 : contender_3 < contender_4.
Proof.
  unfold contender_3, contender_4, "<".
  rewrite unfold_ack; [|lia].
  replace (10002) with (S (S (10000))) by reflexivity.
  rewrite unfold_iter.
  transitivity (S (iter (ack 4 42)
       (S (Init.Nat.of_uint
          (Decimal.D1
             (Decimal.D0
                (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))).
  - apply le_n_S.
    rewrite unfold_iter.
    transitivity (ack 4 42 (S ((Init.Nat.of_uint
          (Decimal.D1
             (Decimal.D0
                (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))).
    +
      exact (ack_4 10000).
    + apply mon_ack_in_b; [lia|].
      assert (geS (iter (ack 4 42))).
      -- apply (geS_ack 5 42); lia.
      -- apply H.
  - apply (geS_ack 4 42); lia.
Qed.
