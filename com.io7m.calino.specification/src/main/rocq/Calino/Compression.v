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

From Stdlib Require Import Strings.String.

Require Import com.io7m.calino.Descriptor.

Inductive compressionMethod : Set :=
  | CompressionUncompressed
  | CompressionBC1
  | CompressionBC2
  | CompressionBC3
  | CompressionBC4
  | CompressionBC5
  | CompressionBC6
  | CompressionBC7
  | CompressionETC1
  | CompressionETC2
  | CompressionEAC
  | CompressionASTC : nat -> nat -> compressionMethod
  | CompressionCustom :
    forall (d : descriptor)
      (blockSizeX : nat)
      (blockSizeY : nat)
      (identifier : nat)
      (align : nat), 0 < align -> compressionMethod.

Definition compressionMethodDescriptor (c : compressionMethod) :=
  match c with
  | CompressionUncompressed       => "UNCOMPRESSED"
  | CompressionBC1                => "BC1"
  | CompressionBC2                => "BC2"
  | CompressionBC3                => "BC3"
  | CompressionBC4                => "BC4"
  | CompressionBC5                => "BC5"
  | CompressionBC6                => "BC6"
  | CompressionBC7                => "BC7"
  | CompressionETC1               => "ETC1"
  | CompressionETC2               => "ETC2"
  | CompressionEAC                => "EAC"
  | CompressionASTC _ _           => "ASTC"
  | CompressionCustom c _ _ _ _ _ => c
  end.

Definition compressionBlockSizeX (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed       => 0
  | CompressionBC1                => 4
  | CompressionBC2                => 4
  | CompressionBC3                => 4
  | CompressionBC4                => 4
  | CompressionBC5                => 4
  | CompressionBC6                => 4
  | CompressionBC7                => 4
  | CompressionETC1               => 4
  | CompressionETC2               => 4
  | CompressionEAC                => 4
  | CompressionASTC x _           => x
  | CompressionCustom _ x _ _ _ _ => x
  end.

Definition compressionBlockSizeY (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed       => 0
  | CompressionBC1                => 4
  | CompressionBC2                => 4
  | CompressionBC3                => 4
  | CompressionBC4                => 4
  | CompressionBC5                => 4
  | CompressionBC6                => 4
  | CompressionBC7                => 4
  | CompressionETC1               => 4
  | CompressionETC2               => 4
  | CompressionEAC                => 4
  | CompressionASTC _ y           => y
  | CompressionCustom _ _ y _ _ _ => y
  end.

Definition compressionSectionIdentifier (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed       => 0
  | CompressionBC1                => 0
  | CompressionBC2                => 0
  | CompressionBC3                => 0
  | CompressionBC4                => 0
  | CompressionBC5                => 0
  | CompressionBC6                => 0
  | CompressionBC7                => 0
  | CompressionETC1               => 0
  | CompressionETC2               => 0
  | CompressionEAC                => 0
  | CompressionASTC _ _           => 0
  | CompressionCustom _ _ _ i _ _ => i
  end.

Definition compressionBlockAlignment (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed       => 0
  | CompressionBC1                => 8
  | CompressionBC2                => 16
  | CompressionBC3                => 16
  | CompressionBC4                => 8
  | CompressionBC5                => 16
  | CompressionBC6                => 16
  | CompressionBC7                => 16
  | CompressionETC1               => 16
  | CompressionETC2               => 16
  | CompressionEAC                => 16
  | CompressionASTC _ _           => 16
  | CompressionCustom _ _ _ _ a _ => a
  end.

Definition compressionIsNotCompressed (c : compressionMethod) : Prop :=
  match c with
  | CompressionUncompressed => True
  | _                       => False
  end.

#[export]
Instance compressionMethodDescribable : describable compressionMethod := {
  descriptorOf c := compressionMethodDescriptor c
}.

