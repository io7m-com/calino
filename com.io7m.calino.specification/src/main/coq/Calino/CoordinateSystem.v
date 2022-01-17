Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

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
  | AxisRIncreasingToward => "RT"%string
  | AxisRIncreasingAway   => "RA"%string
  end.

Definition coordinateAxisSDescribe (c : coordinateAxisS) : descriptor :=
  match c with
  | AxisSIncreasingRight => "SR"%string
  | AxisSIncreasingLeft  => "SL"%string
  end.

Definition coordinateAxisTDescribe (c : coordinateAxisT) : descriptor :=
  match c with
  | AxisTIncreasingDown => "TD"%string
  | AxisTIncreasingUp   => "TU"%string
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

