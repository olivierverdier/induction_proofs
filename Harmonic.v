Require Import Summing.
Require Import Coq.Reals.Reals.
Require Import Omega.
Require Nat.
Local Open Scope R_scope.

(* divergence of harmonic series *)

Definition harmonic (n:nat) := /(INR n + 1).

(* General result about decomposing a sum in chunks *)

Definition chunk_sums u (n:nat):= sum_from u (2^n) (2^n).

Lemma chunk_decomposition: forall u n, sum u (2^n) = sum (chunk_sums u) n + u O.
Proof.
  intros.
  induction n as [|n' IHn'].
  - trivial.
  - replace ((2^(S n'))%nat) with ((2^n' + 2^n')%nat); [|rewrite Nat.pow_succ_r; intuition].
    replace (sum u (2 ^ n' + 2 ^ n')) with (sum u (2^n') + sum_from u (2^n') (2^n')); [|auto using sum_sum_from].
    rewrite IHn'. unfold sum. simpl. unfold chunk_sums. field.
Qed.
  
Lemma harm_decr: forall n m, (n <= m)%nat -> harmonic m <= harmonic n.
Proof.
  intros. unfold harmonic.
  apply Rinv_le_contravar; auto with real. 
Qed.



Lemma pow_INR: forall (x:R) (m:nat),
                 x = INR m
                 -> forall n, x^n = INR (m^n).
Proof.
  intros x m H n.
  induction n as [|n' IHn']; [trivial|]. 
   simpl. rewrite mult_INR. congruence.
Qed.


Lemma tech_nat_pow: forall m n, (1 <= S m ^ n + S m ^ n)%nat.
  intros.
  assert ((1 <= (S m) ^ n)%nat); auto using (le_plus_trans 1 (S m ^ n) (S m ^ n)).
  rewrite <- (Nat.pow_1_l n). apply Nat.pow_le_mono_l. intuition.
Qed.


Lemma tech_INR: forall (x:R) (m:nat),
                          x = INR (S m)
                          -> forall (n:nat),
                               INR((S m)^n + (S m)^n -1) = x^n + x^n - 1.
Proof.
  intros x m H n.
  rewrite minus_INR; [|apply tech_nat_pow]. rewrite plus_INR.
  rewrite (pow_INR x (S m)); [|trivial]. replace (INR 1) with 1; trivial. 
Qed.

Lemma half': forall n, (/2 =  (2^n) * / 2^(S n)).
Proof.
  intros. simpl. field. apply pow_nonzero. discrR.
Qed.


Lemma harmonic_chunk_ge_half: forall n, /2 <= chunk_sums harmonic n.
Proof.
  intros n.
  rewrite (half' n).
  rewrite (pow_INR 2 2%nat); [|trivial].
  replace (/ (2^(S n))) with (harmonic (2 ^ n + 2 ^ n - 1)).
  - apply (lbound_decr harmonic harm_decr (2^n) (2^n)).

  - unfold harmonic. simpl. replace (INR (2^n + 2^n -1)) with (2^n + 2^n - 1).
    * replace (2 ^ n + 2 ^ n - 1 + 1)  with (2*2^n); trivial.
      field.
    * rewrite (tech_INR 2 1%nat); trivial. 
Qed.


Lemma harmonic_O: harmonic 0 = 1.
Proof.
  unfold harmonic.
  replace (INR 0) with 0; [|trivial].
  replace (0 + 1) with 1; auto with real.
Qed.

Lemma sum_harm': forall n, sum (fun k => /2) n + 1 <= sum harmonic (2^n).
Proof.
  intros.
  rewrite chunk_decomposition.
  assert (H: sum (fun _ : nat => / 2) n  <= sum (chunk_sums harmonic) n ). apply (sum_le (fun k => /2) (chunk_sums harmonic)). apply harmonic_chunk_ge_half.
  rewrite harmonic_O.
  auto with real.
Qed.

Theorem sum_harm: forall n, (INR n)/2 +1 <= sum harmonic (2^n).
Proof.
  intros.
  replace (INR n / 2) with (INR n * /2); [|auto with real].
  replace (INR n * /2) with (sum_from (fun k => /2) 0 n); [|auto using sum_from_const].
  apply sum_harm'.
Qed.

  


