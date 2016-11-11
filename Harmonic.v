Require Import Summing.
Require Import Coq.Reals.Reals.
Require Import Omega.
Require Nat.
Local Open Scope R_scope.

(* divergence of harmonic series *)

Definition harmonic (n:nat) := /(INR (S n)).

(* General result about decomposing a sum in chunks *)

Definition chunk_sums u (n:nat):= sum (from u (2^n)) (2^n).

Lemma chunk_decomposition: forall u n, sum u (2^n) = sum (chunk_sums u) n + u O.
Proof.
  intros.
  induction n as [|n' IHn']; [trivial|].
  replace ((2^(S n'))%nat) with ((2^n' + 2^n')%nat) by (rewrite Nat.pow_succ_r; intuition).
  replace (sum u (2 ^ n' + 2 ^ n')) with (sum u (2^n') + sum (from u (2^n')) (2^n')) by (auto using sum_sum_from).
    rewrite IHn'. simpl. unfold chunk_sums. field.
Qed.

Lemma harm_decr: forall n m, (n <= m)%nat -> harmonic m <= harmonic n.
Proof.
  intros.  unfold harmonic. apply Rinv_le_contravar; intuition.
Qed.



Lemma pow_INR: forall (x:R) (m:nat),
                 x = INR m
                 -> forall n, x^n = INR (m^n).
Proof.
  intros x m H n.
  induction n as [|n' IHn']; [trivial|]. 
   simpl. rewrite mult_INR. congruence.
Qed.

Lemma half': forall n, (/2 =  (2^n) * / 2^(S n)).
Proof.
  intros. simpl. field. apply pow_nonzero. discrR.
Qed.


Lemma tech__: forall n, INR (2 * 2 ^ n - 1) + 1 = 2 * 2 ^ n.
Proof.
  intros.
  replace ((2*2^n)%nat) with ((2^(S n))%nat) by intuition.
  assert (2^0 <= 2 ^ S n)%nat.
  -
    apply Nat.pow_le_mono_r; intuition.
  -
  rewrite minus_INR; intuition.
  replace (INR 1) with 1 by intuition.
  replace (2*2^n) with (2^(S n)) by intuition.
  rewrite (pow_INR 2 2%nat). field. intuition. 
Qed.


Lemma tech_: forall n, harmonic (2 ^ n + 2 ^ n - 1) = / 2 ^ S n.
Proof.
  intros.
  unfold harmonic.
  simpl (2^(S n)).
  replace (2 ^ n + 2 ^ n)%nat with (2* 2 ^ n)%nat by omega.  
  assert (INR (S (2 * 2 ^ n - 1)) = 2 * 2 ^ n); intuition.
  rewrite S_INR.  apply tech__.
Qed.

  

Lemma harmonic_chunk_ge_half: forall n, /2 <= chunk_sums harmonic n.
Proof.
  intros n.
  rewrite (half' n).
  rewrite (pow_INR 2 2%nat); [|trivial].
  rewrite <- tech_.
  replace (harmonic (2 ^ n + 2 ^ n - 1)) with (from harmonic (2^n) (2^n - 1)) by (unfold from; intuition).
  apply lbound_decr.
  unfold from.  intros. apply harm_decr. intuition.
Qed.


Lemma sum_harm': forall n, sum (fun k => /2) n + 1 <= sum harmonic (2^n).
Proof.
  intros.
  rewrite chunk_decomposition.
  assert (sum (fun _ : nat => / 2) n  <= sum (chunk_sums harmonic) n ).
  apply sum_le. apply harmonic_chunk_ge_half.
  replace (harmonic 0) with 1; intuition.
Qed.

Theorem sum_harm: forall n, (INR n)/2 +1 <= sum harmonic (2^n).
Proof.
  intros.
  replace (INR n / 2) with (INR n * /2) by intuition.
  replace (INR n * /2) with (sum (from (fun k => /2) 0) n).
  - apply sum_harm'.
  - refine (sum_const _ _).
Qed.

  


