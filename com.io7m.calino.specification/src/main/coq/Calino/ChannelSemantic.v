Require Import Coq.Strings.String.

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
  | CSRed      => "R"
  | CSGreen    => "G"
  | CSBlue     => "B"
  | CSAlpha    => "A"
  | CSDepth    => "D"
  | CSStencil  => "S"
  | CSExponent => "E"
  | CSUnused   => "X"
  end.

#[export]
Instance channelSemanticDescribable : describable channelSemantic := {
  descriptorOf c := channelSemanticDescribe c
}.

