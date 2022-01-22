Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
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
  | nil        => ""
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

Theorem channelLayoutPackingBitsDiv8 : forall c,
  divisible8 (channelLayoutPackingBits (c)).
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

Lemma natAddNonzero : forall (n m : nat), n <> 0 -> m + n <> 0.
Proof.
  intros n m HnZ.
  destruct m; simpl; auto.
Qed.

Lemma channelDescriptionsBitsNonEmptyNonZero : forall (c : list channelDescription),
  c <> nil -> channelDescriptionsBitsTotal c <> 0.
Proof.
  intros c HnotNil.
  induction c as [|a b]. {
    contradiction.
  } {
    simpl.
    assert (cdBits a <> 0) as HbitsNZ
      by apply (cdBitsNonzero a).
    assert (channelDescriptionsBitsTotal b + cdBits a <> 0) as Hnz2. {
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

