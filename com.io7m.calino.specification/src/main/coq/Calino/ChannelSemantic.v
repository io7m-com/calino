Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Calino.Descriptor.

Inductive channelSemantic : Set :=
  | CSRed
  | CSGreen
  | CSBlue
  | CSAlpha
  | CSDepth
  | CSStencil
  | CSExponent
  | CSUnused.

Definition channelSemanticDescribe (c : channelSemantic) : descriptor :=
  match c with
  | CSRed      => "R"%string
  | CSGreen    => "G"%string
  | CSBlue     => "B"%string
  | CSAlpha    => "A"%string
  | CSDepth    => "D"%string
  | CSStencil  => "S"%string
  | CSExponent => "E"%string
  | CSUnused   => "X"%string
  end.

#[export]
Instance channelSemanticDescribable : describable channelSemantic := {
  descriptorOf c := channelSemanticDescribe c
}.
