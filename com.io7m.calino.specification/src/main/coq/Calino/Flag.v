Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.Descriptor.

Import ListNotations.

Inductive flag : Set :=
  | FlagAlphaPremultiplied
  | FlagCustom : descriptor → flag.

Definition flagDescribe (f : flag) : descriptor :=
  match f with
  | FlagAlphaPremultiplied => "ALPHA_PREMULTIPLIED"
  | FlagCustom d           => d
  end.

#[export]
Instance flagDescribable : describable flag := {
  descriptorOf f := flagDescribe f
}.

Inductive flagSet : Set := {
  flags      : list flag;
  flagsNoDup : NoDup flags;
}.

