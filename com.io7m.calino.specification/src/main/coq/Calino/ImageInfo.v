Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.Divisible8.
Require Import Calino.StringUtility.
Require Import Calino.Descriptor.
Require Import Calino.ChannelDescription.
Require Import Calino.ChannelSemantic.
Require Import Calino.ChannelType.
Require Import Calino.Compression.
Require Import Calino.SuperCompression.
Require Import Calino.ColorSpace.
Require Import Calino.Flag.
Require Import Calino.ByteOrder.
Require Import Calino.CoordinateSystem.
Require Import Calino.ImageSize.

Open Scope program_scope.

Record imageInfo : Set := ImageInfo {
  imageSize                   : imageSize3D;
  imageChannelsLayout         : channelLayoutDescription;
  imageChannelsType           : channelType;
  imageCompressionMethod      : compressionMethod;
  imageSuperCompressionMethod : superCompressionMethod;
  imageCoordinateSystem       : coordinateSystem;
  imageColorSpace             : colorSpace;
  imageFlags                  : flagSet;
  imageByteOrder              : byteOrder
}.

Definition imageSizeX := sizeX ∘ imageSize.

Definition imageSizeY := sizeY ∘ imageSize.

Definition imageSizeZ := sizeZ ∘ imageSize.

Definition imageFlagSet := flags ∘ imageFlags.

Definition imageInfoTexelBlockAlignment (i : imageInfo) :=
  let c := imageCompressionMethod i in
    match c with
    | CompressionUncompressed => channelLayoutDescriptionBits (imageChannelsLayout i) / 8
    | _                       => compressionBlockAlignment c
    end.

Theorem imageInfoTexelBlockAlignmentPositive : ∀ i,
  0 < imageInfoTexelBlockAlignment i.
Proof.
  intros i.
  unfold imageInfoTexelBlockAlignment.
  destruct (imageCompressionMethod i) eqn:Hm.
  - assert (8 <= channelLayoutDescriptionBits (imageChannelsLayout i)) as Hle8
      by (apply (channelLayoutDescriptionBitsLe8)).
    apply (Nat.div_le_lower_bound (channelLayoutDescriptionBits (imageChannelsLayout i)) 8 1).
    discriminate.
    rewrite Nat.mul_1_r.
    exact Hle8.
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - repeat (constructor).
  - auto.
Qed.

Theorem imageInfoTexelBlockAlignmentNonZero : ∀ i,
  0 ≠ imageInfoTexelBlockAlignment i.
Proof.
  intros i.
  apply Lt.lt_0_neq.
  apply imageInfoTexelBlockAlignmentPositive.
Qed.
