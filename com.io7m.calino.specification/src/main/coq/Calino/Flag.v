Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Calino.Descriptor.

Inductive flag : Set :=
  | FlagAlphaPremultiplied
  | FlagCustom : descriptor -> flag.

Definition flagDescribe (f : flag) : descriptor :=
  match f with
  | FlagAlphaPremultiplied => "ALPHA_PREMULTIPLIED"%string
  | FlagCustom d           => d
  end.
