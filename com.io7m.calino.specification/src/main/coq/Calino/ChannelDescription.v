Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import Calino.ChannelSemantic.
Require Import Calino.Descriptor.
Require Import Calino.StringUtility.
Require Import Calino.Divisible8.

Import ListNotations.

Set Mangle Names.

Inductive channelDescription : Set := channelDescriptionMake {
  cdSemantic    : channelSemantic;
  cdBits        : nat;
  cdBitsNonzero : cdBits <> 0
}.

Definition channelDescriptionDescribe (c : channelDescription) : descriptor :=
  append (descriptorOf (cdSemantic c)) (stringOfNat (cdBits c)).

#[export]
Instance channelDescriptionDescribable : describable channelDescription := {
  descriptorOf c := channelDescriptionDescribe c
}.

Fixpoint channelDescriptionsDescribe (c : list channelDescription) : descriptor :=
  match c with
  | nil        => ""%string
  | cons d nil => channelDescriptionDescribe d
  | cons d e   => append (channelDescriptionDescribe d) (append ":" (channelDescriptionsDescribe e))
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

Definition channelLayoutPackingDescribe (c : channelLayoutPacking) : descriptor :=
  match c with
  | CLPack8  => "p8"%string
  | CLPack16 => "p16"%string
  | CLPack32 => "p32"%string
  | CLPack64 => "p64"%string
  end.

#[export]
Instance channelLayoutPackingDescribable : describable channelLayoutPacking := {
  descriptorOf c := channelLayoutPackingDescribe c
}.

Definition channelDescriptionsNotEmpty (xs: list channelDescription) : Prop := xs <> nil.

Definition channelDescriptionBitsDivisible8 (c : channelDescription) : Prop :=
  divisible8 (cdBits c).

Fixpoint channelDescriptionsBitsTotal (c : list channelDescription) : nat :=
  match c with
  | nil         => 0
  | (x :: rest) => (cdBits x) + (channelDescriptionsBitsTotal rest)
  end.

Lemma natAddNonzero : forall (n m : nat), n <> 0 -> m + n <> 0.
Proof.
  intros n m HnZ.
  destruct m; simpl; auto.
Qed.

Lemma channelDescriptionsBitsNonEmptyNonZero : forall (c : list channelDescription),
  c <> nil -> channelDescriptionsBitsTotal c <> 0.
Proof.
  intros c HnotNil.
  induction c as [|a b].
    contradiction.
    simpl.
    assert (cdBits a <> 0) as HbitsNZ.
      apply (cdBitsNonzero a).
      assert (channelDescriptionsBitsTotal b + cdBits a <> 0) as Hnz2.
        apply natAddNonzero.
        exact HbitsNZ.
      rewrite (Nat.add_comm) in Hnz2.
      exact Hnz2.
Qed.

Inductive channelLayoutDescriptionUnpacked : Set := CLDUMake {
  clduChannels   : list channelDescription;
  clduInvariants : Forall channelDescriptionBitsDivisible8 clduChannels;
}.

Definition channelLayoutDescriptionUnpackedDescribe (c : channelLayoutDescriptionUnpacked) : descriptor :=
  channelDescriptionsDescribe (clduChannels c).

#[export]
Instance channelLayoutDescriptionUnpackedDescribable : describable channelLayoutDescriptionUnpacked := {
  descriptorOf c := channelLayoutDescriptionUnpackedDescribe c
}.

Inductive channelLayoutDescriptionPacked : Set := CLDPMake {
  cldpChannels   : list channelDescription;
  cldpPacking    : channelLayoutPacking;
  cldpInvariants : channelDescriptionsBitsTotal cldpChannels = channelLayoutPackingBits cldpPacking
}.

Definition channelLayoutDescriptionPackedDescribe (c : channelLayoutDescriptionPacked) : descriptor :=
  let packing := descriptorOf (cldpPacking c) in
  let channels := channelDescriptionsDescribe (cldpChannels c) in
    append packing (append "|" channels).

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
