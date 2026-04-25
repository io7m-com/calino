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
From Stdlib Require Import Init.Byte.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Program.Basics.

Require Import com.io7m.calino.Metadata.
Require Import com.io7m.calino.ArrayMipMap.
Require Import com.io7m.calino.CubeMipMap.
Require Import com.io7m.calino.MipMap.
Require Import com.io7m.calino.ImageInfo.
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
Require Import com.io7m.calino.ThreeDMipMap.

Require Import com.io7m.octetorder.OctetOrder.

Require Import com.io7m.entomos.Alignment.
Require Import com.io7m.entomos.Binary.

Import ListNotations.

Open Scope program_scope.
Open Scope string_scope.

Set Mangle Names.

Definition byteOrderDescribe (b : octetOrder) : descriptor :=
  match b with
  | OctetOrderBig    => "BIG_ENDIAN"
  | OctetOrderLittle => "LITTLE_ENDIAN"
  end.

#[export]
Instance byteOrderDescribable : describable octetOrder := {
  descriptorOf f := byteOrderDescribe f
}.

Definition binaryExpMipMap (m : mipMap) : binaryExp := BiRecord [
  ("mipMapLevel",            u32 (mipMapLevel m));
  ("mipMapDataOffset",       u64 (mipMapOffset m));
  ("mipMapSizeUncompressed", u64 (mipMapSizeUncompressed m));
  ("mipMapSizeCompressed",   u64 (mipMapSizeCompressed m));
  ("mipMapCRC32",            u32 (mipMapCRC32 m))
].

Remark binaryExpMipMapSize : forall m, binarySize (binaryExpMipMap m) = 32.
Proof. reflexivity. Qed.

Definition binaryExpMipMaps (m : mipMapList) : binaryExp :=
  BiArray (map binaryExpMipMap (mipMaps m)).

Definition binaryExpImage2D
  (i : imageInfo)
  (m : mipMapList)
: binaryExp :=
  let imageDataStart := mipMapOffset (mipMapFirst m) in
  let encMips        := binaryExpMipMaps m in
  let encMipsSize    := binarySize encMips in
  let encMipsPad     := imageDataStart - encMipsSize in
  let imageSize      := mipMapImageDataSizeTotal m in
  let imageSize16    := asMultipleOf16 imageSize in
    BiRecord [
      ("mipMaps", encMips);
      ("mipPad",  BiReserve encMipsPad);
      ("mipData", BiReserve imageSize16)
    ].

Definition binaryExpImage2DSection
  (i : imageInfo)
  (m : mipMapList)
: binaryExp := BiRecord [
  ("id",   u64 0x434C4E5F49324421);
  ("size", u64 (binarySizePadded16 (binaryExpImage2D i m)));
  ("data", binaryExpImage2D i m)
].

Definition binaryExpArrayMipMap (m : arrayMipMap) : binaryExp := BiRecord [
  ("arrayMipMapLevel",            u32 (arrayMipMapLevel (arrayMipMapIndex m)));
  ("arrayMipMapLayer",            u32 (arrayMipMapLayer (arrayMipMapIndex m)));
  ("arrayMipMapDataOffset",       u64 (arrayMipMapOffset m));
  ("arrayMipMapSizeUncompressed", u64 (arrayMipMapSizeUncompressed m));
  ("arrayMipMapSizeCompressed",   u64 (arrayMipMapSizeCompressed m));
  ("arrayMipMapCRC32",            u32 (arrayMipMapCRC32 m))
].

Remark binaryExpArrayMipMapSize : forall m, binarySize (binaryExpArrayMipMap m) = 36.
Proof. reflexivity. Qed.

Definition binaryExpArrayMipMaps (m : arrayMipMapList) : binaryExp :=
  BiArray (map binaryExpArrayMipMap (arrayMipMaps m)).

Definition binaryExpImageArray
  (i : imageInfo)
  (m : arrayMipMapList)
: binaryExp :=
  let imageDataStart := arrayMipMapOffset (arrayMipMapFirst m) in
  let encMips        := binaryExpArrayMipMaps m in
  let encMipsSize    := binarySize encMips in
  let encMipsPad     := imageDataStart - encMipsSize in
  let imageSize      := arrayMipMapImageDataSizeTotal m in
  let imageSize16    := asMultipleOf16 imageSize in
    BiRecord [
      ("arrayMipMaps", encMips);
      ("arrayMipPad",  BiReserve encMipsPad);
      ("arrayMipData", BiReserve imageSize16)
    ].

Definition binaryExpImageArraySection
  (i : imageInfo)
  (m : arrayMipMapList)
: binaryExp := BiRecord [
  ("id",   u64 0x434C4E5F41525221);
  ("size", u64 (binarySizePadded16 (binaryExpImageArray i m)));
  ("data", binaryExpImageArray i m)
].

Definition binaryExpCubeMipMapFace (m : cubeMapFace) : binaryExp := BiRecord [
  ("cubeFaceDataOffset",       u64 (cubeFaceOffset m));
  ("cubeFaceSizeUncompressed", u64 (cubeFaceSizeUncompressed m));
  ("cubeFaceSizeCompressed",   u64 (cubeFaceSizeCompressed m));
  ("cubeFaceCRC32",            u32 (cubeFaceCRC32 m))
].

Remark binaryExpCubeMipMapFaceSize : forall m, binarySize (binaryExpCubeMipMapFace m) = 28.
Proof. reflexivity. Qed.

Definition binaryExpCubeMipMap (m : cubeMipMap) : binaryExp := BiRecord [
  ("cubeMipMapLevel",    u32 (cubeMapLevel m));
  ("cubeMipMapFacePosX", binaryExpCubeMipMapFace (cubeMapFaceXPos m));
  ("cubeMipMapFaceNegX", binaryExpCubeMipMapFace (cubeMapFaceXNeg m));
  ("cubeMipMapFacePosY", binaryExpCubeMipMapFace (cubeMapFaceYPos m));
  ("cubeMipMapFaceNegY", binaryExpCubeMipMapFace (cubeMapFaceYNeg m));
  ("cubeMipMapFacePosZ", binaryExpCubeMipMapFace (cubeMapFaceZPos m));
  ("cubeMipMapFaceNegZ", binaryExpCubeMipMapFace (cubeMapFaceZNeg m))
].

Remark binaryExpCubeMipMapSize : forall m, binarySize (binaryExpCubeMipMap m) = 172.
Proof. reflexivity. Qed.

Definition binaryExpCubeMipMaps (m : cubeMipMapList) : binaryExp :=
  BiArray (map binaryExpCubeMipMap (cubeMipMaps m)).

Definition binaryExpImageCubeMap
  (i : imageInfo)
  (m : cubeMipMapList)
: binaryExp :=
  let imageDataStart := cubeFaceOffset (cubeMapFaceXPos (cubeMipMapsFirst m)) in
  let encMips        := binaryExpCubeMipMaps m in
  let encMipsSize    := binarySize encMips in
  let encMipsPad     := imageDataStart - encMipsSize in
  let imageSize      := cubeMipMapImageDataSizeTotal m in
  let imageSize16    := asMultipleOf16 imageSize in
    BiRecord [
      ("cubeMipMaps", encMips);
      ("cubeMipPad",  BiReserve encMipsPad);
      ("cubeMipData", BiReserve imageSize16)
    ].

Definition binaryExpImageCubeSection
  (i : imageInfo)
  (m : cubeMipMapList)
: binaryExp := BiRecord [
  ("id",   u64 0x434C4E5F43554245);
  ("size", u64 (binarySizePadded16 (binaryExpImageCubeMap i m)));
  ("data", binaryExpImageCubeMap i m)
].

Definition binaryExpCompression (c : compressionMethod) : binaryExp := BiRecord [
  ("descriptor",        utf8 (descriptorOf c));
  ("sectionIdentifier", u64 (compressionSectionIdentifier c));
  ("blockSizeX",        u32 (compressionBlockSizeX c));
  ("blockSizeY",        u32 (compressionBlockSizeY c));
  ("blockAlignment",    u32 (compressionBlockAlignment c))
].

Definition binaryExpSuperCompression (c : superCompressionMethod) : binaryExp := BiRecord [
  ("descriptor",        utf8 (descriptorOf c));
  ("sectionIdentifier", u64 (superCompressionSectionIdentifier c))
].

Definition binaryExpImageInfo (i : imageInfo) : binaryExp := BiRecord [
  ("sizeX",            u32 (imageSizeX i));
  ("sizeY",            u32 (imageSizeY i));
  ("sizeZ",            u32 (imageSizeZ i));
  ("channelsLayout",   utf8 (descriptorOf (imageChannelsLayout i)));
  ("channelsType",     utf8 (descriptorOf (imageChannelsType i)));
  ("compression",      binaryExpCompression (imageCompressionMethod i));
  ("superCompression", binaryExpSuperCompression (imageSuperCompressionMethod i));
  ("coordinateSystem", utf8 (descriptorOf (imageCoordinateSystem i)));
  ("colorSpace",       utf8 (descriptorOf (imageColorSpace i)));
  ("flags",            BiArray (map (utf8 ∘ descriptorOf) (imageFlagSet i)));
  ("byteOrder",        utf8 (descriptorOf (imageByteOrder i)))
].

Definition binaryExpFileHeader : binaryExp := BiRecord [
  ("id",           u64 0x89434C4E0D0A1A0A);
  ("versionMajor", u32 1);
  ("versionMinor", u32 0)
].

Definition binaryExpImageInfoSection (i : imageInfo) : binaryExp := BiRecord [
  ("id",   u64 0x434C4E49494E464F);
  ("size", u64 (binarySizePadded16 (binaryExpImageInfo i)));
  ("data", binaryExpImageInfo i)
].

Definition binaryExpMetadataValue (m : metadataValue) : binaryExp := BiRecord [
  ("key",   utf8 (mKey m));
  ("value", utf8 (mValue m))
].

Definition binaryExpMetadata (m : metadata) : binaryExp :=
  BiArray (map binaryExpMetadataValue (mValues m)).

Definition binaryExpMetadataSection (m : metadata) : binaryExp := BiRecord [
  ("id",   u64 0x434C4E5F4D455441);
  ("size", u64 (binarySizePadded16 (binaryExpMetadata m)));
  ("data", binaryExpMetadata m)
].

Definition binaryEndSection : binaryExp := BiRecord [
  ("id",   u64 0x434c4e5f454e4421);
  ("size", u64 0)
].

Definition binaryExp3DMipMap (m : threeDMipMap) : binaryExp := BiRecord [
  ("threeDMipMapLevel",            u32 (threeDMipMapLevel (threeDMipMapIndex m)));
  ("threeDMipMapDepth",            u32 (threeDMipMapDepth (threeDMipMapIndex m)));
  ("threeDMipMapDataOffset",       u64 (threeDMipMapOffset m));
  ("threeDMipMapSizeUncompressed", u64 (threeDMipMapSizeUncompressed m));
  ("threeDMipMapSizeCompressed",   u64 (threeDMipMapSizeCompressed m));
  ("threeDMipMapCRC32",            u32 (threeDMipMapCRC32 m))
].

Remark binaryExp3DMipMapSize : forall m, binarySize (binaryExp3DMipMap m) = 36.
Proof. reflexivity. Qed.

Definition binaryExp3DMipMaps (m : threeDMipMapList) : binaryExp :=
  BiArray (map binaryExp3DMipMap (threeDMipMaps m)).

Definition binaryExpImage3D
  (i : imageInfo)
  (m : threeDMipMapList)
: binaryExp :=
  let imageDataStart := threeDMipMapOffset (threeDMipMapFirst m) in
  let encMips        := binaryExp3DMipMaps m in
  let encMipsSize    := binarySize encMips in
  let encMipsPad     := imageDataStart - encMipsSize in
  let imageSize      := threeDMipMapImageDataSizeTotal m in
  let imageSize16    := asMultipleOf16 imageSize in
    BiRecord [
      ("threeDMipMaps", encMips);
      ("threeDMipPad",  BiReserve encMipsPad);
      ("threeDMipData", BiReserve imageSize16)
    ].

Definition binaryExpImage3DSection
  (i : imageInfo)
  (m : threeDMipMapList)
: binaryExp := BiRecord [
  ("id",   u64 0x434C4E5F41525221);
  ("size", u64 (binarySizePadded16 (binaryExpImage3D i m)));
  ("data", binaryExpImage3D i m)
].
