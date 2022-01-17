Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.

Set Mangle Names.

Definition divisible8 (x : nat) : Prop := modulo x 8 = 0.

Lemma divisiblity8Add : forall (x y : nat),
  divisible8 x -> divisible8 y -> divisible8 (x + y).
Proof.
  intros x y Hx Hy.
  unfold divisible8 in *.
  destruct y as [|y].
    (* If y = 0, then this matches one of our assumptions already. *)
    rewrite Nat.add_0_r; exact Hx.

    (* Otherwise, the following property always holds given that the divisor is 8. *)
    assert ((x mod 8 + S y) mod 8 = (x + S y) mod 8) as Heq.
      apply (Nat.add_mod_idemp_l x (S y) 8).
      discriminate.

    (* x mod 8 = 0 *)
    rewrite Hx in Heq.
    (* 0 + S y = S y *)
    rewrite Nat.add_0_l in Heq.
    rewrite <- Heq.
    exact Hy.
Qed.
