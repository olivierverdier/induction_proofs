Require Import Summing.
Require Import Coq.Reals.Reals.
Require Import Omega.
Local Open Scope R_scope.


(* Solution of some standard sum induction exercises *)

Ltac rec_finish IH := simpl; rewrite IH; try field; try assumption.

Theorem sum_nat: forall n:nat, (sum (fun k => INR k) n) = INR n * (INR n-1)/2.
Proof.
  intros n. unfold sum.
  induction n as [| n']. 
  * simpl. field.
  * simpl sum_from. rewrite S_INR. rec_finish IHn'.
Qed.

Lemma sum_geometric: forall n x, (1 - x <> 0) -> (sum (fun k => x^k)) n = (1 - x^n)/(1-x).
Proof.
  intros. unfold sum.
  induction n as [|n'].
  * simpl. field. assumption.
  * rec_finish IHn'.
Qed.

Definition tmp_u (k:nat) := (2 * INR k + 1)^2.

Lemma sum_odd_square: forall n, sum tmp_u n = INR n * (4*(INR n)^2 - 1)  / 3.
Proof.
  intros. unfold sum.
  induction n as [|n'].
  * simpl. field.
  * simpl sum_from. rewrite IHn'. unfold tmp_u. rewrite S_INR. field.
Qed.



Theorem sum_k_Sk: forall n, sum (fun k => INR k * (INR k+1)) n = (INR n -1) * (INR n) * (INR n+1) /3.
Proof.
  intros. unfold sum.
  induction n as [|n'].
  * simpl. field.
  * simpl sum_from. rewrite S_INR. rec_finish IHn'. 
Qed.