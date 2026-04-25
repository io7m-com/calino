(*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Nat.

Require Import com.io7m.calino.ChannelSemantic.
Require Import com.io7m.calino.Descriptor.
Require Import com.io7m.calino.StringUtility.

Require Import com.io7m.entomos.Divisible.

Import ListNotations.

Set Mangle Names.

Definition divisible8 (x : nat) : Prop :=
  modulo x 8 = 0.

Inductive channelDescription : Set := channelDescriptionMake {
  cdSemantic    : channelSemantic;
  cdBits        : nat;
  cdBitsNonzero : 0 <> cdBits
}.

Definition channelDescriptionDescribe (c : channelDescription) : descriptor :=
  descriptorOf (cdSemantic c) ++ stringOfNat (cdBits c).

#[export]
Instance channelDescriptionDescribable : describable channelDescription := {
  descriptorOf c := channelDescriptionDescribe c
}.

Fixpoint channelDescriptionsDescribe (c : list channelDescription) : descriptor :=
  match c with
  | nil        => ""
  | cons d nil => channelDescriptionDescribe d
  | cons d e   => (channelDescriptionDescribe d) ++ ":" ++ (channelDescriptionsDescribe e)
  end.

Inductive channelLayoutPacking : Set :=
  | CLPack8
  | CLPack16
  | CLPack32
  | CLPack64.

Definition channelLayoutPackingBits (c : channelLayoutPacking) : nat :=
  match c with
  | CLPack8  => 8
  | CLPack16 => 16
  | CLPack32 => 32
  | CLPack64 => 64
  end.

Theorem channelLayoutPackingBitsDiv8 : forall c, divisible8 (channelLayoutPackingBits (c)).
Proof.
  intros c.
  destruct c; reflexivity.
Qed.

Definition channelLayoutPackingDescribe (c : channelLayoutPacking) : descriptor :=
  match c with
  | CLPack8  => "p8"
  | CLPack16 => "p16"
  | CLPack32 => "p32"
  | CLPack64 => "p64"
  end.

#[export]
Instance channelLayoutPackingDescribable : describable channelLayoutPacking := {
  descriptorOf c := channelLayoutPackingDescribe c
}.

Definition channelDescriptionBitsDivisible8 (c : channelDescription) : Prop :=
  divisible8 (cdBits c).

Fixpoint channelDescriptionsBitsTotal (c : list channelDescription) : nat :=
  match c with
  | nil         => 0
  | (x :: rest) => (cdBits x) + (channelDescriptionsBitsTotal rest)
  end.

Lemma natAddNonzero : forall (n m : nat), 0 <> n -> 0 <> m + n.
Proof.
  intros n m HnZ.
  destruct m; simpl; auto.
Qed.

Lemma channelDescriptionsBitsNonEmptyNonZero : forall (c : list channelDescription),
  nil <> c -> 0 <> channelDescriptionsBitsTotal c.
Proof.
  intros c HnotNil.
  induction c as [|a b]. {
    contradiction.
  } {
    simpl.
    assert (0 <> cdBits a) as HbitsNZ
      by apply (cdBitsNonzero a).
    assert (0 <> channelDescriptionsBitsTotal b + cdBits a) as Hnz2. {
      apply natAddNonzero.
      exact HbitsNZ.
    }
    rewrite (Nat.add_comm) in Hnz2.
    exact Hnz2.
  }
Qed.

Inductive channelLayoutDescriptionUnpacked : Set := CLDUMake {
  uChannels         : list channelDescription;
  uChannelsNonEmpty : [] <> uChannels;
  uInvariants       : Forall channelDescriptionBitsDivisible8 uChannels;
}.

Definition channelLayoutDescriptionUnpackedDescribe (c : channelLayoutDescriptionUnpacked) : descriptor :=
  channelDescriptionsDescribe (uChannels c).

#[export]
Instance channelLayoutDescriptionUnpackedDescribable : describable channelLayoutDescriptionUnpacked := {
  descriptorOf c := channelLayoutDescriptionUnpackedDescribe c
}.

Inductive channelLayoutDescriptionPacked : Set := CLDPMake {
  pChannels         : list channelDescription;
  pChannelsNonEmpty : [] <> pChannels;
  pPacking          : channelLayoutPacking;
  pInvariants       : channelDescriptionsBitsTotal pChannels = channelLayoutPackingBits pPacking
}.

Definition channelLayoutDescriptionPackedDescribe (c : channelLayoutDescriptionPacked) : descriptor :=
  let packing := descriptorOf (pPacking c) in
  let channels := channelDescriptionsDescribe (pChannels c) in
    packing ++ "|" ++ channels.

#[export]
Instance channelLayoutDescriptionPackedDescribable : describable channelLayoutDescriptionPacked := {
  descriptorOf c := channelLayoutDescriptionPackedDescribe c
}.

Inductive channelLayoutDescription : Set :=
  | ChannelLayoutDescriptionUnpacked : channelLayoutDescriptionUnpacked -> channelLayoutDescription
  | ChannelLayoutDescriptionPacked   : channelLayoutDescriptionPacked   -> channelLayoutDescription.

Definition channelLayoutDescriptionDescribe (c : channelLayoutDescription) : descriptor :=
  match c with
  | ChannelLayoutDescriptionPacked p   => descriptorOf p
  | ChannelLayoutDescriptionUnpacked u => descriptorOf u
  end.

#[export]
Instance channelLayoutDescriptionDescribable : describable channelLayoutDescription := {
  descriptorOf c := channelLayoutDescriptionDescribe c
}.

Definition channelLayoutDescriptionBits (c : channelLayoutDescription) : nat :=
  match c with
  | ChannelLayoutDescriptionUnpacked u =>
    channelDescriptionsBitsTotal (uChannels u)
  | ChannelLayoutDescriptionPacked p =>
    channelDescriptionsBitsTotal (pChannels p)
  end.

Lemma channelLayoutDescriptionBitsAdd : forall d ds,
  channelDescriptionsBitsTotal (d :: ds) =
    (cdBits d) + (channelDescriptionsBitsTotal ds).
Proof. intros d ds. reflexivity. Qed.

Lemma divisiblity8Add : forall (x y : nat),
  divisible8 x -> divisible8 y -> divisible8 (x + y).
Proof.
  intros x y Hx Hy.
  unfold divisible8 in *.
  apply divisiblityNAdd.
  discriminate.
  trivial.
  trivial.
Qed.

Theorem channelLayoutDescriptionBitsDivisible8 : forall (c : channelLayoutDescription),
  divisible8 (channelLayoutDescriptionBits c).
Proof.
  intros c.
  destruct c as [u|p]. {
    assert (Forall channelDescriptionBitsDivisible8 (uChannels u)) as Hf8
      by (apply uInvariants).
    unfold channelLayoutDescriptionBits.
    induction (uChannels u) as [|d ds IHu]. {
      reflexivity.
    } {
      rewrite channelLayoutDescriptionBitsAdd.
      assert (divisible8 (channelDescriptionsBitsTotal ds)) as Hdsdiv8. {
        assert (Forall channelDescriptionBitsDivisible8 ds) as Hfac
          by (apply (Forall_inv_tail (a := d) (l := ds) Hf8)).
        apply (IHu Hfac).
      }
      assert (divisible8 (cdBits d)) as Hdivbits
        by (apply (Forall_inv (a := d) (l := ds) Hf8)).
      apply (divisiblity8Add (cdBits d) (channelDescriptionsBitsTotal ds) Hdivbits Hdsdiv8).
    }
  } {
    simpl.
    assert (channelDescriptionsBitsTotal (pChannels p) = channelLayoutPackingBits (pPacking p))
      as Hbeq by (apply pInvariants).
    rewrite Hbeq.
    apply channelLayoutPackingBitsDiv8.
  }
Qed.

Theorem channelLayoutDescriptionBitsLe8 : forall (c : channelLayoutDescription),
  8 <= channelLayoutDescriptionBits c.
Proof.
  intros c.
  assert (divisible8 (channelLayoutDescriptionBits c)) as Hdiv8
    by (apply (channelLayoutDescriptionBitsDivisible8 c)).
  unfold divisible8 in Hdiv8.

  destruct c as [u|p].
  - simpl.
    destruct (uChannels u) as [|ch0 chs] eqn:Hcheq.
    -- symmetry in Hcheq.
       assert ([] <> uChannels u) as Hne by (apply (uChannelsNonEmpty u)).
       contradiction.
    -- unfold channelLayoutDescriptionBits in Hdiv8.
       rewrite Nat.Lcm0.mod_divide in Hdiv8.
       rewrite <- Hcheq.
       apply (Nat.divide_pos_le 8 (channelDescriptionsBitsTotal (uChannels u))).
       rewrite Hcheq.
       simpl.
       assert (0 < cdBits ch0) as HbitnZ. {
         apply Nat.neq_0_lt_0.
         symmetry.
         apply (cdBitsNonzero ch0).
       }
       apply Nat.add_pos_l.
       exact HbitnZ.
       exact Hdiv8.
  - simpl.
    rewrite (pInvariants p).
    destruct (pPacking p) eqn:Hpack.
    -- constructor.
    -- repeat (constructor).
    -- repeat (constructor).
    -- repeat (constructor).
Qed.

