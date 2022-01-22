Require Import Coq.Strings.String.

Require Import Calino.Descriptor.

Inductive channelType : Set :=
  | CTFixedPointNormalizedUnsigned
  | CTFixedPointNormalizedSigned
  | CTScaledUnsigned
  | CTScaledSigned
  | CTIntegerUnsigned
  | CTIntegerSigned
  | CTFloatIEEE754
  | CTCustom : descriptor -> channelType.

Definition channelTypeDescribe (c : channelType) : descriptor :=
  match c with
  | CTFixedPointNormalizedUnsigned => "FIXED_POINT_NORMALIZED_UNSIGNED"
  | CTFixedPointNormalizedSigned   => "FIXED_POINT_NORMALIZED_SIGNED"
  | CTScaledUnsigned               => "SCALED_UNSIGNED"
  | CTScaledSigned                 => "SCALED_SIGNED"
  | CTIntegerUnsigned              => "INTEGER_UNSIGNED"
  | CTIntegerSigned                => "INTEGER_SIGNED"
  | CTFloatIEEE754                 => "FLOATING_POINT_IEEE754"
  | CTCustom d                     => d
  end.

#[export]
Instance channelTypeDescribable : describable channelType := {
  descriptorOf c := channelTypeDescribe c
}.

