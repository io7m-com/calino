Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Init.Byte.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Basics.
Require Import Coq.Unicode.Utf8_core.

Definition asMultipleOf (size q : nat) (Hnz : 0 ≠ q) : nat :=
  let r := size / q in
    match Nat.ltb_spec0 r q with
    | ReflectT _ _ => (r + 1) * q
    | ReflectF _ _ => r * q
    end.

Lemma p0not4 : 0 ≠ 4.
Proof. discriminate. Qed.

Lemma p0not16 : 0 ≠ 16.
Proof. discriminate. Qed.

Definition asMultipleOf4 (size : nat) : nat :=
  asMultipleOf size 4 p0not4.

Definition asMultipleOf16 (size : nat) : nat :=
  asMultipleOf size 16 p0not16.

Lemma asMultipleOfMod : ∀ s q (Hneq : 0 ≠ q), (asMultipleOf s q Hneq) mod q = 0.
Proof.
  intros s q Hneq.
  unfold asMultipleOf.
  destruct (Nat.ltb_spec0 (s / q) q) as [Hlt|H1].
  - apply (Nat.mod_mul (s / q + 1) q (Nat.neq_sym _ _ Hneq)).
  - apply (Nat.mod_mul (s / q) q (Nat.neq_sym _ _ Hneq)).
Qed.
