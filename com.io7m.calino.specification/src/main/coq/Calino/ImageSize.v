Require Import Coq.Unicode.Utf8_core.

Record imageSize3D : Set := ImageSize3D {
  sizeX     : nat;
  sizeY     : nat;
  sizeZ     : nat;
  sizeXnot0 : 0 ≠ sizeX;
  sizeYnot0 : 0 ≠ sizeY;
  sizeZnot0 : 0 ≠ sizeZ;
}.

