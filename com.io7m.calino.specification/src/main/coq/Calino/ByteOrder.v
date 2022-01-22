Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.Divisible8.

Import ListNotations.

Inductive byteOrder : Set :=
  | ByteOrderBig
  | ByteOrderLittle.

Inductive bit : Set :=
  | B0
  | B1.

Inductive octet : Set :=
  | OctExact  : bit → bit → bit → bit → bit → bit → bit → bit → octet
  | OctRemain : bit → bit → bit → bit → bit → bit → bit → bit → octet.

Definition octetIsRemainder (o : octet): Prop :=
  match o with
  | OctExact  _ _ _ _ _ _ _ _ => False
  | OctRemain _ _ _ _ _ _ _ _ => True
  end.

Definition octetIsExact (o : octet): Prop :=
  match o with
  | OctExact  _ _ _ _ _ _ _ _ => True
  | OctRemain _ _ _ _ _ _ _ _ => False
  end.

Lemma octetIsRemainderNotExact : ∀ (o : octet), octetIsRemainder o → ¬octetIsExact o.
Proof.
  intros o Hrem Hfalse.
  destruct o; contradiction.
Qed.

Lemma octetIsExactNotRemainder : ∀ (o : octet), octetIsExact o → ¬octetIsRemainder o.
Proof.
  intros o Hrem Hfalse.
  destruct o; contradiction.
Qed.

Inductive bitsOctetsHasRemainder : list octet → Prop :=
  | BOHasRemainder : ∀ (prefix : list octet) (o : octet),
    Forall octetIsExact prefix →
      octetIsRemainder o →
        bitsOctetsHasRemainder (prefix ++ o :: []).

Fixpoint octetsBigEndianAux
  (bits   : list bit)
  (octets : list octet)
: list octet :=
  match bits with
  | (b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: rest) => 
    octets ++ [OctExact b7 b6 b5 b4 b3 b2 b1 b0] ++ octetsBigEndianAux rest []
  | (b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: rest) => 
    octets ++ [OctRemain b7 b6 b5 b4 b3 b2 b1 B0] ++ octetsBigEndianAux rest []
  | (b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: rest) => 
    octets ++ [OctRemain b7 b6 b5 b4 b3 b2 B0 B0] ++ octetsBigEndianAux rest []
  | (b7 :: b6 :: b5 :: b4 :: b3 :: rest) => 
    octets ++ [OctRemain b7 b6 b5 b4 b3 B0 B0 B0] ++ octetsBigEndianAux rest []
  | (b7 :: b6 :: b5 :: b4 :: rest) => 
    octets ++ [OctRemain b7 b6 b5 b4 B0 B0 B0 B0] ++ octetsBigEndianAux rest []
  | (b7 :: b6 :: b5 :: rest) => 
    octets ++ [OctRemain b7 b6 b5 B0 B0 B0 B0 B0] ++ octetsBigEndianAux rest []
  | (b7 :: b6 :: rest) => 
    octets ++ [OctRemain b7 b6 B0 B0 B0 B0 B0 B0] ++ octetsBigEndianAux rest []
  | (b7 :: rest) => 
    octets ++ [OctRemain b7 B0 B0 B0 B0 B0 B0 B0] ++ octetsBigEndianAux rest []
  | [] => 
    octets
  end.

Definition octetsBigEndian (bits : list bit) : list octet :=
  octetsBigEndianAux bits [].

Definition octetsLittleEndian (bits : list bit) : list octet :=
  rev (octetsBigEndianAux bits []).

Definition listInduction8 :
  ∀ (A : Type),
  ∀ (P : list A → Prop),
  P [] →
  (∀ (b0                      : A), P (b0 :: [])) →
  (∀ (b1 b0                   : A), P (b1 :: b0 :: [])) →
  (∀ (b2 b1 b0                : A), P (b2 :: b1 :: b0 :: [])) →
  (∀ (b3 b2 b1 b0             : A), P (b3 :: b2 :: b1 :: b0 :: [])) →
  (∀ (b4 b3 b2 b1 b0          : A), P (b4 :: b3 :: b2 :: b1 :: b0 :: [])) →
  (∀ (b5 b4 b3 b2 b1 b0       : A), P (b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: [])) →
  (∀ (b6 b5 b4 b3 b2 b1 b0    : A), P (b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: [])) →
  (∀ (b7 b6 b5 b4 b3 b2 b1 b0 : A) (rest : list A), P rest → P (b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: rest)) →
  ∀ (L : list A), P L :=
  λ A P P0 P1 P2 P3 P4 P5 P6 P7 P8,
  fix f (l : list A) :=
    match l with
    | []                                                     => P0
    | x0 :: []                                               => P1 x0
    | (x0 :: x1 :: [])                                       => P2 x0 x1
    | (x0 :: x1 :: x2 :: [])                                 => P3 x0 x1 x2
    | (x0 :: x1 :: x2 :: x3 :: [])                           => P4 x0 x1 x2 x3
    | (x0 :: x1 :: x2 :: x3 :: x4 :: [])                     => P5 x0 x1 x2 x3 x4
    | (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: [])               => P6 x0 x1 x2 x3 x4 x5
    | (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: [])         => P7 x0 x1 x2 x3 x4 x5 x6
    | (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) => P8 x0 x1 x2 x3 x4 x5 x6 x7 rest (f rest)
    end.

Lemma app_non_empty : ∀ (A : Type) (xs : list A) (y : A),
  xs ++ [y] ≠ [].
Proof.
  intros A xs y.
  unfold not.
  destruct xs as [|z zs].
    intros Hfalse; inversion Hfalse.
    intros Hfalse; inversion Hfalse.
Qed.

Lemma app_list_implies_eq : ∀ (A : Type) (x y : A) (xs : list A),
  xs ++ [x] = [y] → xs = [] ∧ x = y.
Proof.
  intros A x y xs Happ.
  induction xs as [|z zs] eqn:Hxe.
  - constructor. reflexivity.
    rewrite (app_nil_l [x]) in Happ.
    injection Happ as Heq; exact Heq.
  - inversion Happ.
    assert (zs ++ [x] ≠ []) by (apply app_non_empty).
    contradiction.
Qed.

Lemma p8notZ : 8 ≠ 0.
Proof. discriminate. Qed.

Lemma list_mod8_0 : ∀ (A : Type) (xs : list A) (n7 n6 n5 n4 n3 n2 n1 n0 : A),
  divisible8 (length xs) → divisible8 (length (n7 :: n6 :: n5 :: n4 :: n3 :: n2 :: n1 :: n0 :: xs)).
Proof.
  intros A xs n7 n6 n5 n4 n3 n2 n1 n0 Hlen8.
  unfold divisible8 in *.
  assert (n7 :: n6 :: n5 :: n4 :: n3 :: n2 :: n1 :: n0 :: xs 
       = (n7 :: n6 :: n5 :: n4 :: n3 :: n2 :: n1 :: n0 :: []) ++ xs) as HlistEq
          by reflexivity.
  rewrite HlistEq.
  rewrite app_length.
  assert (length [n7; n6; n5; n4; n3; n2; n1; n0] = 8) as Hprefix8 by reflexivity.
  rewrite Hprefix8.
  rewrite <- (Nat.add_mod_idemp_l 8 (length xs) 8 p8notZ).
  rewrite (Nat.mod_same 8 p8notZ).
  rewrite (Nat.add_0_l).
  exact Hlen8.
Qed.

Lemma list_mod8_1 : ∀ (A : Type) (xs : list A) (n7 n6 n5 n4 n3 n2 n1 n0 : A),
  divisible8 (length (n7 :: n6 :: n5 :: n4 :: n3 :: n2 :: n1 :: n0 :: xs)) → divisible8 (length xs).
Proof.
  intros A xs n7 n6 n5 n4 n3 n2 n1 n0 Hlen8.
  unfold divisible8 in *.
  assert (n7 :: n6 :: n5 :: n4 :: n3 :: n2 :: n1 :: n0 :: xs 
       = (n7 :: n6 :: n5 :: n4 :: n3 :: n2 :: n1 :: n0 :: []) ++ xs) as HlistEq
          by reflexivity.
  rewrite HlistEq in Hlen8.
  rewrite app_length in Hlen8.
  assert (length [n7; n6; n5; n4; n3; n2; n1; n0] = 8) as Hprefix8 by reflexivity.
  rewrite Hprefix8 in Hlen8.
  rewrite <- (Nat.add_mod_idemp_l 8 (length xs) 8 p8notZ) in Hlen8.
  rewrite (Nat.mod_same 8 p8notZ) in Hlen8.
  rewrite (Nat.add_0_l) in Hlen8.
  exact Hlen8.
Qed.

Theorem list_mod8 : ∀ (A : Type) (xs : list A) (n7 n6 n5 n4 n3 n2 n1 n0 : A),
  divisible8 (length xs) ↔ divisible8 (length (n7 :: n6 :: n5 :: n4 :: n3 :: n2 :: n1 :: n0 :: xs)).
Proof.
  intros A xs n7 n6 n5 n4 n3 n2 n1 n0.
  constructor. 
  - apply list_mod8_0.
  - apply list_mod8_1.
Qed.

Theorem octetsBigEndianLengthDivisibleAllExact : ∀ (b : list bit),
  divisible8 (length b) → Forall octetIsExact (octetsBigEndian b).
Proof.
  intros b Hlen8.
  unfold octetsBigEndian.
  induction b using listInduction8.
  - constructor.
  - inversion Hlen8.
  - inversion Hlen8.
  - inversion Hlen8.
  - inversion Hlen8.
  - inversion Hlen8.
  - inversion Hlen8.
  - inversion Hlen8.
  - simpl.
    rewrite <- list_mod8 in Hlen8.
    assert (Forall octetIsExact (octetsBigEndianAux b []))   as HallExact by (apply (IHb Hlen8)).
    assert (octetIsExact (OctExact b7 b6 b5 b4 b3 b2 b1 b0)) as Hexact    by constructor.
    apply (@Forall_cons octet octetIsExact (OctExact b7 b6 b5 b4 b3 b2 b1 b0) (octetsBigEndianAux b []) Hexact HallExact).
Qed.

Theorem octetsBigEndianLengthDivisibleNoRemainder : ∀ (b : list bit),
  Forall octetIsExact (octetsBigEndian b) → ¬ bitsOctetsHasRemainder (octetsBigEndian b).
Proof.
  intros b HallExact.
  unfold octetsBigEndian.
  intro Hfalse.
  inversion Hfalse as [prefix o HprefixAllExact HoIsRemainder HprefixEq].
  unfold octetsBigEndian in HallExact.

  (* We know that everything in the list is exact. *)
  (* We can show that o must be in this list according to HprefixEq. *)
  assert (In o (octetsBigEndianAux b [])) as HoInB. {
    assert (In o (prefix ++ [o])) as HoInPrefix by (apply (in_elt o prefix [])).
    rewrite HprefixEq in HoInPrefix.
    exact HoInPrefix.
  }

  (* And because o is in the list, it must be exact. *)
  assert (octetIsExact o) as HoIsExact. {
    rewrite Forall_forall in HallExact.
    apply (HallExact o HoInB).
  }

  (* There is a contradiction; o cannot be both exact and a remainder. *)
  apply (octetIsExactNotRemainder o HoIsExact HoIsRemainder).
Qed.


