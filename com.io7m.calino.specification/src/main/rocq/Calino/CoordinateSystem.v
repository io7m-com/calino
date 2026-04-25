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

Inductive coordinateAxisR : Set :=
  | AxisRIncreasingToward
  | AxisRIncreasingAway.

Inductive coordinateAxisS : Set :=
  | AxisSIncreasingRight
  | AxisSIncreasingLeft.

Inductive coordinateAxisT : Set :=
  | AxisTIncreasingDown
  | AxisTIncreasingUp.

Definition coordinateAxisRDescribe (c : coordinateAxisR) : descriptor :=
  match c with
  | AxisRIncreasingToward => "RT"
  | AxisRIncreasingAway   => "RA"
  end.

Definition coordinateAxisSDescribe (c : coordinateAxisS) : descriptor :=
  match c with
  | AxisSIncreasingRight => "SR"
  | AxisSIncreasingLeft  => "SL"
  end.

Definition coordinateAxisTDescribe (c : coordinateAxisT) : descriptor :=
  match c with
  | AxisTIncreasingDown => "TD"
  | AxisTIncreasingUp   => "TU"
  end.

#[export]
Instance coordinateAxisRDescribable : describable coordinateAxisR := {
  descriptorOf c := coordinateAxisRDescribe c
}.

#[export]
Instance coordinateAxisSDescribable : describable coordinateAxisS := {
  descriptorOf c := coordinateAxisSDescribe c
}.

#[export]
Instance coordinateAxisTDescribable : describable coordinateAxisT := {
  descriptorOf c := coordinateAxisTDescribe c
}.

Inductive coordinateSystem : Set :=
  CoordinateSystem : coordinateAxisR -> coordinateAxisS -> coordinateAxisT -> coordinateSystem.

Definition coordinateSystemDescribe (c : coordinateSystem) : descriptor :=
  match c with
  | CoordinateSystem r s t =>
    descriptorOf r ++ ":" ++ descriptorOf s ++ ":" ++ descriptorOf t
  end.

#[export]
Instance coordinateSystemDescribable : describable coordinateSystem := {
  descriptorOf c := coordinateSystemDescribe c
}.

