Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.Descriptor.

Inductive superCompressionMethod : Set :=
  | SuperCompressionUncompressed
  | SuperCompressionLZ4
  | SuperCompressionCustom : descriptor → nat → superCompressionMethod.

Definition superCompressionMethodDescriptor (c : superCompressionMethod) :=
  match c with
  | SuperCompressionUncompressed => "UNCOMPRESSED"
  | SuperCompressionLZ4          => "LZ4"
  | SuperCompressionCustom c _   => c
  end.

Definition superCompressionIsNotCompressed (c : superCompressionMethod) : Prop :=
  match c with
  | SuperCompressionUncompressed => True
  | _                            => False
  end.

Definition superCompressionSectionIdentifier (c : superCompressionMethod) : nat :=
  match c with
  | SuperCompressionUncompressed => 0
  | SuperCompressionLZ4          => 0
  | SuperCompressionCustom _ i   => i
  end.

#[export]
Instance superCompressionMethodDescribable : describable superCompressionMethod := {
  descriptorOf c := superCompressionMethodDescriptor c
}.

