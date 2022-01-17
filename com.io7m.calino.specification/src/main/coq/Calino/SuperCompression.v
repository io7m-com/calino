Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Calino.Descriptor.

Inductive superCompressionMethod : Set :=
  | SuperCompressionUncompressed
  | SuperCompressionLZ4
  | SuperCompressionCustom : descriptor -> nat -> superCompressionMethod.

Definition superCompressionMethodDescriptor (c : superCompressionMethod) :=
  match c with
  | SuperCompressionUncompressed => "UNCOMPRESSED"%string
  | SuperCompressionLZ4          => "LZ4"%string
  | SuperCompressionCustom c _   => c
  end.

Definition superCompressionIsNotCompressed (c : superCompressionMethod) : Prop :=
  match c with
  | SuperCompressionUncompressed => True
  | _                            => False
  end.

#[export]
Instance superCompressionMethodDescribable : describable superCompressionMethod := {
  descriptorOf c := superCompressionMethodDescriptor c
}.
