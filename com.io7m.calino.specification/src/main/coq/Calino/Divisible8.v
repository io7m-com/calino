Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.

(* Set Mangle Names. *)

Definition divisible8 (x : nat) : Prop :=
  modulo x 8 = 0.

Theorem divisiblityNAdd : ∀ (x y z : nat),
  0 ≠ z → x mod z = 0 → y mod z = 0 → (x + y) mod z = 0.
Proof.
  intros x y z Hz Hx Hy.
  destruct y as [|y].
    (* If y = 0, then this matches one of our assumptions already. *)
    rewrite Nat.add_0_r; exact Hx.
    (* Otherwise, the following property always holds given that the divisor is ≠ 0. *)
    assert ((x mod z + S y) mod z = (x + S y) mod z) as Heq.
      apply (Nat.add_mod_idemp_l x (S y) z).
      apply (Nat.neq_sym 0 z Hz).
    (* x mod z = 0 *)
    rewrite Hx in Heq.
    (* 0 + S y = S y *)
    rewrite Nat.add_0_l in Heq.
    rewrite <- Heq.
    exact Hy.
Qed.

Theorem divisibilityNFoldPlus : ∀ z xs,
  0 ≠ z →
    Forall (λ n, n mod z = 0) xs →
      (fold_right plus 0 xs) mod z = 0.
Proof.
  intros z xs Hnz HforAll.
  induction xs as [|y ys].
  - apply (Nat.mod_0_l z (Nat.neq_sym 0 z Hnz)).
  - assert (fold_right add 0 (y :: ys) = y + fold_right add 0 ys) as Hfoldeq by reflexivity.
    rewrite Hfoldeq.
    assert (fold_right add 0 ys mod z = 0) as Hfoldeq2. {
      apply IHys.
      apply (@Forall_inv_tail nat (λ n : nat, n mod z = 0) y ys HforAll).
    }
    rewrite divisiblityNAdd.
    reflexivity.
    exact Hnz.
    apply (@Forall_inv nat (λ n : nat, n mod z = 0) y ys HforAll).
    exact Hfoldeq2.
Qed.

Theorem divisiblity8Add : ∀ (x y : nat),
  divisible8 x → divisible8 y → divisible8 (x + y).
Proof.
  intros x y Hx Hy.
  unfold divisible8 in *.
  apply divisiblityNAdd.
  discriminate.
  trivial.
  trivial.
Qed.

