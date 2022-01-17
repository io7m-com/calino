Require Import Coq.PArith.PArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

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

Record imageInfo : Set := ImageInfo {
  imageSizeX                  : nat;
  imageSizeY                  : nat;
  imageSizeZ                  : nat;
  imageSizeInvariants         : imageSizeX <> 0 /\ imageSizeY <> 0 /\ imageSizeZ <> 0;
  imageChannelsLayout         : channelLayoutDescription;
  imageChannelsType           : channelType;
  imageCompressionMethod      : compressionMethod;
  imageSuperCompressionMethod : superCompressionMethod;
  imageCoordinateSystem       : coordinateSystem;
  imageColorSpace             : colorSpace;
  imageFlags                  : list flag;
  imageByteOrder              : byteOrder
}.
