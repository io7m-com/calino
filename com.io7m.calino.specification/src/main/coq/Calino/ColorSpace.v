Require Import Coq.Strings.String.

Require Import Calino.Descriptor.

Inductive colorSpace : Set :=
  | CSLinear
  | CSsRGB
  | CSCustom : descriptor -> colorSpace.

Definition colorSpaceDescribe (c : colorSpace) : descriptor :=
  match c with
  | CSLinear   => "LINEAR"
  | CSsRGB     => "SRGB"
  | CSCustom d => d
  end.

#[export]
Instance colorSpaceDescribable : describable colorSpace := {
  descriptorOf c := colorSpaceDescribe c
}.
