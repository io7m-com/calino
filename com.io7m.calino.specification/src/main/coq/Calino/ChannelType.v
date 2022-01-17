Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Calino.Descriptor.

Inductive channelType : Set :=
  | CTFixedPointNormalizedUnsigned
  | CTFixedPointNormalizedSigned
  | CTScaledUnsigned
  | CTScaledSigned
  | CTIntegerUnsigned
  | CTIntegerSigned
  | CTFloatIEEE754Unsigned
  | CTFloatIEEE754Signed
  | CTCustom : descriptor -> channelType.

Definition channelTypeDescribe (c : channelType) : descriptor :=
  match c with
  | CTFixedPointNormalizedUnsigned => "FIXED_POINT_NORMALIZED_UNSIGNED"%string
  | CTFixedPointNormalizedSigned   => "FIXED_POINT_NORMALIZED_SIGNED"%string
  | CTScaledUnsigned               => "SCALED_UNSIGNED"%string
  | CTScaledSigned                 => "SCALED_SIGNED"%string
  | CTIntegerUnsigned              => "INTEGER_UNSIGNED"%string
  | CTIntegerSigned                => "INTEGER_SIGNED"%string
  | CTFloatIEEE754Unsigned         => "FLOATING_POINT_IEEE754_UNSIGNED"%string
  | CTFloatIEEE754Signed           => "FLOATING_POINT_IEEE754_SIGNED"%string
  | CTCustom d                     => d
  end.

#[export]
Instance channelTypeDescribable : describable channelType := {
  descriptorOf c := channelTypeDescribe c
}.
