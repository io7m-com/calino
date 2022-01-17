Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Calino.Descriptor.

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
  | CompressionCustom : descriptor -> nat -> nat -> nat -> nat -> compressionMethod.

Definition compressionMethodDescriptor (c : compressionMethod) :=
  match c with
  | CompressionUncompressed     => "UNCOMPRESSED"%string
  | CompressionBC1              => "BC1"%string
  | CompressionBC2              => "BC2"%string
  | CompressionBC3              => "BC3"%string
  | CompressionBC4              => "BC4"%string
  | CompressionBC5              => "BC5"%string
  | CompressionBC6              => "BC6"%string
  | CompressionBC7              => "BC7"%string
  | CompressionETC1             => "ETC1"%string
  | CompressionETC2             => "ETC2"%string
  | CompressionEAC              => "EAC"%string
  | CompressionASTC _ _         => "ASTC"%string
  | CompressionCustom c _ _ _ _ => c
  end.

Definition compressionBlockSizeX (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed     => 0
  | CompressionBC1              => 4
  | CompressionBC2              => 4
  | CompressionBC3              => 4
  | CompressionBC4              => 4
  | CompressionBC5              => 4
  | CompressionBC6              => 4
  | CompressionBC7              => 4
  | CompressionETC1             => 4
  | CompressionETC2             => 4
  | CompressionEAC              => 4
  | CompressionASTC x _         => x
  | CompressionCustom _ x _ _ _ => x
  end.

Definition compressionBlockSizeY (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed     => 0
  | CompressionBC1              => 4
  | CompressionBC2              => 4
  | CompressionBC3              => 4
  | CompressionBC4              => 4
  | CompressionBC5              => 4
  | CompressionBC6              => 4
  | CompressionBC7              => 4
  | CompressionETC1             => 4
  | CompressionETC2             => 4
  | CompressionEAC              => 4
  | CompressionASTC _ y         => y
  | CompressionCustom _ _ y _ _ => y
  end.

Definition compressionSectionIdentifier (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed     => 0
  | CompressionBC1              => 0
  | CompressionBC2              => 0
  | CompressionBC3              => 0
  | CompressionBC4              => 0
  | CompressionBC5              => 0
  | CompressionBC6              => 0
  | CompressionBC7              => 0
  | CompressionETC1             => 0
  | CompressionETC2             => 0
  | CompressionEAC              => 0
  | CompressionASTC _ _         => 0
  | CompressionCustom _ _ _ i _ => i
  end.

Definition compressionBlockAlignment (c : compressionMethod) : nat :=
  match c with
  | CompressionUncompressed     => 0
  | CompressionBC1              => 8
  | CompressionBC2              => 16
  | CompressionBC3              => 16
  | CompressionBC4              => 8
  | CompressionBC5              => 16
  | CompressionBC6              => 16
  | CompressionBC7              => 16
  | CompressionETC1             => 16
  | CompressionETC2             => 16
  | CompressionEAC              => 16
  | CompressionASTC _ _         => 16
  | CompressionCustom _ _ _ _ a => a
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
