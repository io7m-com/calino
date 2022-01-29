Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.

Open Scope string_scope.

Import ListNotations.

Inductive metadataValue : Set := MetadataValue {
  mKey   : string;
  mValue : string
}.

Inductive metadata : Set := Metadata {
  mValues : list metadataValue
}.

