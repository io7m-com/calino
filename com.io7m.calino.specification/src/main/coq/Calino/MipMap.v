Require Import Coq.Lists.List.

Import ListNotations.

Inductive mipMap : Set := MipMap {
  mipMapLevel            : nat;
  mipMapOffset           : nat;
  mipMapSizeCompressed   : nat;
  mipMapSizeUncompressed : nat;
  mipMapCRC32            : nat
}.

Inductive mipMapListIsSorted : list mipMap -> Prop :=
  | MipsOne   : forall m, mipMapListIsSorted [m]
  | MipsCons  : forall mm0 mm1 mxs, 
    mipMapLevel mm1 = S (mipMapLevel mm0) ->
      mipMapListIsSorted (mm0 :: mxs) ->
        mipMapListIsSorted (mm1 :: mm0 :: mxs).

Inductive mipMapList : Set := MipMapList {
  mipMaps            : list mipMap;
  mipMapListNonEmpty : nil <> mipMaps;
  mipMapListSorted   : mipMapListIsSorted mipMaps
}.
