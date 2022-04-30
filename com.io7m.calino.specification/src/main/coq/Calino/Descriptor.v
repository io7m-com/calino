Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.
Open Scope char_scope.

Definition descriptor := string.

Class describable (A : Set) := {
  descriptorOf : A -> descriptor
}.

