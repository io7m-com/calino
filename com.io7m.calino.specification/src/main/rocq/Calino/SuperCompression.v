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

Inductive superCompressionMethod : Set :=
  | SuperCompressionUncompressed
  | SuperCompressionLZ4
  | SuperCompressionDEFLATE
  | SuperCompressionCustom : descriptor -> nat -> superCompressionMethod.

Definition superCompressionMethodDescriptor (c : superCompressionMethod) :=
  match c with
  | SuperCompressionUncompressed => "UNCOMPRESSED"
  | SuperCompressionLZ4          => "LZ4"
  | SuperCompressionDEFLATE      => "DEFLATE"
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
  | SuperCompressionDEFLATE      => 0
  | SuperCompressionCustom _ i   => i
  end.

#[export]
Instance superCompressionMethodDescribable : describable superCompressionMethod := {
  descriptorOf c := superCompressionMethodDescriptor c
}.

