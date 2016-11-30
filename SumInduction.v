Require Import Summing.
Require Import Coq.Reals.Reals.
Require Import Omega.
Local Open Scope R_scope.


(* Solution of some standard sum induction exercises *)

Hint Resolve S_INR.

Theorem sum_nat: forall n:nat, (sum (fun k => INR k) n) = INR n * (INR n-1)/2.
Proof.
  intros n. 
  induction n as [| n']. 
  * simpl. field.
  * simpl sum. replace (INR (S n')) with (INR n' + 1) by intuition.  rewrite IHn'. field.
Qed.


Lemma sum_geometric': forall m n x, (1 - x <> 0) -> sum (from (fun k => x^k) m) n = x^m * (1 - x^n)/(1-x).
Proof.
  intros.
  induction n as [|n' IHn].
  - simpl. field. trivial.
  - simpl. rewrite IHn. unfold from. replace (x^(m+n')) with (x^m * x^n') by intuition. field; trivial. 
Qed.


Definition odd_square k := (2 * INR k + 1)^2.


Lemma sum_odd_square: forall n, sum odd_square n = INR n * (4*(INR n)^2 - 1)  / 3.
Proof.
  intros.
  induction n as [|n'].
  * simpl. field.
  * simpl sum. rewrite IHn'. unfold odd_square. replace (INR (S n')) with (INR n' + 1) by intuition.  field.
Qed.



Theorem sum_k_Sk: forall n, sum (fun k => INR k * (INR k+1)) n = (INR n -1) * (INR n) * (INR n+1) /3.
Proof.
  intros.
  induction n as [|n'].
  * simpl. field.
  * simpl sum. replace (INR (S n')) with (INR n' + 1) by intuition. rewrite IHn'. field.
Qed.

Local Close Scope R_scope.
