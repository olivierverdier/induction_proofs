Require Import Coq.Reals.Reals.
Require Nat.


Local Open Scope R_scope.

Require Import Omega.

Require Import Summing.

(* Check that the induction definition is the same as the Fixpoint one *)

Fixpoint sum_from' (u:nat -> R) (m:nat) (N:nat) :=
  match N with
    | O => 0
    | S N' => sum_from' u m N' + u (m + N')%nat
  end.

Lemma sum_from_check: forall u m N, sum (from u m) N = sum_from' u m N.
  Proof.
    intros.
    induction N as [|N'].
    reflexivity.
    simpl. rewrite IHN'. unfold from. reflexivity.
Qed.


Fixpoint sum' (u: nat -> R) (N: nat) :=
  match N with
    | O => 0
    | S N' => sum u N' + u N'
  end.

Lemma sum_check: forall u n, sum u n = sum' u n.
Proof.
  intros. unfold sum. induction n as [|n']; trivial.
Qed.