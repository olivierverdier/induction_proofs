Require Import Coq.Reals.Reals.
Require Nat.


Local Open Scope R_scope.

Require Import Omega.


Fixpoint sum_from (u:nat -> R) (m:nat) (N:nat) :=
  match N with
    | O => 0
    | S N' => sum_from u m N' + u (m + N')%nat
  end.

Definition sum (u: nat -> R) := sum_from u 0.

Fixpoint sum' (u: nat -> R) (N: nat) :=
  match N with
    | O => 0
    | S N' => sum u N' + u N'
  end.

Lemma sum_check: forall u n, sum u n = sum' u n.
Proof.
  intros. unfold sum. induction n as [|n']; trivial.
Qed.

(* Some general theorems about sums *)

Lemma lmint:
  forall (u:nat -> R) (m0 N:nat) (l:R),
    (forall k:nat, (k < N)%nat -> l <= u (m0 + k)%nat)
    -> forall n:nat, (n <= N)%nat
                     -> INR n * l <= sum_from u m0 n.
Proof.
  intros.
  induction n as [|n']; auto with real.
  assert (H1: (n' <= N)%nat). auto with real.
  apply IHn' in H1.

  simpl sum_from. rewrite S_INR.

  replace ((INR n' +1)*l) with (INR n' * l + l); try field.
  assert (l <= u (m0 + n')%nat); auto with real. 
Qed.


Lemma lbound_decr:
  forall (u:nat -> R),
    (forall n1 n2, (n1 <= n2)%nat -> (u n2 <= u n1))
    -> forall m0 n, INR n * (u (m0 + n - 1)%nat)  <= sum_from u m0 n.
Proof.
  intros u H m0 n.
  destruct n.
  - auto with real.
  - replace (m0 + S n - 1)%nat with ((m0 + n)%nat); intuition. 
    refine (lmint u m0 (S n)  (u(m0+n)%nat) _ _ _); intuition.
Qed.

Lemma sum_zero: forall u, sum u 0 = 0.
Proof. trivial. Qed.

Lemma sum_from_zero: forall u m, sum_from u m 0 = 0.
Proof. trivial. Qed.

Lemma sum_sum_from:
  forall u n m,
    sum u (n+m)%nat = sum u n + sum_from u n m.
Proof.
  intros.
  unfold sum.
  induction m as [|m' IHm'].
  - rewrite <- plus_n_O. auto with real. 
  - rewrite Nat.add_succ_r.  simpl.  rewrite IHm'. auto with real.
Qed.

Lemma sum_le: forall u v, (forall n, u n <= v n) -> forall m N, sum_from u m N <= sum_from v m N.
Proof.
  intros.
  induction N as [|N' IHN'].
  - auto with real. 
  - simpl sum_from. pose (H (m+N')%nat). auto with real.
Qed.

Lemma sum_from_const: forall x m n, sum_from (fun k => x) m n = INR n *x.
Proof.
  intros.
  induction n as [|n' IHn'].
  - simpl. field.
  - simpl sum_from. rewrite IHn'. rewrite S_INR. field.
Qed.