Require Import Coq.Reals.Reals.
Require Nat.


Local Open Scope R_scope.

Require Import Omega.

Definition from (u:nat -> R) (m:nat) (n:nat): R :=
  u (m+n)%nat.

Definition sum (u:nat -> R) (N:nat): R.
Proof.
  elim N.
  - exact 0.
  - intros N' x. exact (x + u N').
Defined.


(* Some general theorems about sums *)

Lemma lmint:
  forall u N l,
    (forall k, (k < N)%nat -> l <= u k)
                     -> forall n, (n <= N)%nat -> INR n * l <= sum u n.
Proof.
  intros.
  induction n as [|n']; intuition.
  assert (H1: (n' <= N)%nat). auto with real.
  apply IHn' in H1.

  simpl sum. rewrite S_INR.

  replace ((INR n' +1)*l) with (INR n' * l + l) by field.
  assert (l <= u n'); intuition.
Qed.


Lemma lbound_decr:
  forall u,
    (forall n1 n2, (n1 <= n2)%nat -> (u n2 <= u n1))
    -> forall n, INR n * (u (n - 1)%nat)  <= sum u n.
Proof.
  intros u H n.
  destruct n; intuition.
  replace (S n - 1)%nat with n by intuition. 
  refine (lmint _ (S n) _ _ _  _); intuition.
Qed.


Lemma sum_sum_from:
  forall u m n,
    sum u (n+m)%nat = sum u n + sum (from u n) m.
Proof.
  intros.
  induction m as [|m' IHm'].
  - replace (n+0)%nat with n; intuition.
  - rewrite Nat.add_succ_r.  simpl.  rewrite IHm'. intuition.
Qed.

Lemma sum_le: forall u v, (forall n, u n <= v n) -> forall N, sum u N <= sum v N.
Proof.
  intros.
  induction N as [|N' IHN']; [intuition|].
  simpl sum. intuition. 
Qed.

Lemma sum_const: forall x n, sum (fun k => x) n = INR n *x.
Proof.
  intros.
  induction n as [|n' IHn']; [intuition|].
  simpl sum. rewrite IHn'. rewrite S_INR. field.
Qed.