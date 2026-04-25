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

From Stdlib Require Import PArith.PArith.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Nat.

Require Import com.io7m.calino.StringUtility.
Require Import com.io7m.calino.Descriptor.
Require Import com.io7m.calino.ChannelDescription.
Require Import com.io7m.calino.ChannelSemantic.
Require Import com.io7m.calino.ChannelType.
Require Import com.io7m.calino.Compression.
Require Import com.io7m.calino.SuperCompression.
Require Import com.io7m.calino.ColorSpace.
Require Import com.io7m.calino.Flag.
Require Import com.io7m.calino.CoordinateSystem.
Require Import com.io7m.calino.ImageSize.

Require Import com.io7m.octetorder.OctetOrder.

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
  imageByteOrder              : octetOrder
}.

Definition imageSizeX :=
  sizeX ∘ imageSize.

Definition imageSizeY :=
  sizeY ∘ imageSize.

Definition imageSizeZ :=
  sizeZ ∘ imageSize.

Definition imageFlagSet :=
  flags ∘ imageFlags.

Definition imageInfoTexelBlockAlignment (i : imageInfo) :=
  let c := imageCompressionMethod i in
    match c with
    | CompressionUncompressed => channelLayoutDescriptionBits (imageChannelsLayout i) / 8
    | _                       => compressionBlockAlignment c
    end.

Theorem imageInfoTexelBlockAlignmentPositive : forall i,
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

Theorem imageInfoTexelBlockAlignmentNonZero : forall i,
  0 <> imageInfoTexelBlockAlignment i.
Proof.
  intros i.
  symmetry.
  rewrite Nat.neq_0_lt_0.
  apply imageInfoTexelBlockAlignmentPositive.
Qed.

