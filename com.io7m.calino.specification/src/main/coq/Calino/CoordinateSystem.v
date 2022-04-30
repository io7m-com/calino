Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.Descriptor.

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
  CoordinateSystem : coordinateAxisR → coordinateAxisS → coordinateAxisT → coordinateSystem.

Definition coordinateSystemDescribe (c : coordinateSystem) : descriptor :=
  match c with
  | CoordinateSystem r s t =>
    descriptorOf r ++ ":" ++ descriptorOf s ++ ":" ++ descriptorOf t
  end.

#[export]
Instance coordinateSystemDescribable : describable coordinateSystem := {
  descriptorOf c := coordinateSystemDescribe c
}.

