Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.ImageSize.

Import ListNotations.

Inductive cubeMapFace : Set := CubeMapFace {
  cubeFaceOffset           : nat;
  cubeFaceSizeCompressed   : nat;
  cubeFaceSizeUncompressed : nat;
  cubeFaceCRC32            : nat
}.

Inductive cubeMipMap : Set := CubeMipMap {
  cubeMapLevel     : nat;
  cubeMapFaceXPos  : cubeMapFace;
  cubeMapFaceXNeg  : cubeMapFace;
  cubeMapFaceYPos  : cubeMapFace;
  cubeMapFaceYNeg  : cubeMapFace;
  cubeMapFaceZPos  : cubeMapFace;
  cubeMapFaceZNeg  : cubeMapFace
}.

Definition cubeFaceExtent (f : cubeMapFace) : nat :=
  cubeFaceOffset f + cubeFaceSizeCompressed f.

Inductive cubeOffsetsSorted : list cubeMipMap → Prop :=
  | CMMSizeOne  : ∀ m,
    cubeFaceExtent (cubeMapFaceXPos m) < cubeFaceOffset (cubeMapFaceXNeg m) →
    cubeFaceExtent (cubeMapFaceXNeg m) < cubeFaceOffset (cubeMapFaceYPos m) →
    cubeFaceExtent (cubeMapFaceYPos m) < cubeFaceOffset (cubeMapFaceYNeg m) →
    cubeFaceExtent (cubeMapFaceYNeg m) < cubeFaceOffset (cubeMapFaceZPos m) →
    cubeFaceExtent (cubeMapFaceZPos m) < cubeFaceOffset (cubeMapFaceZNeg m) →
      cubeOffsetsSorted [m]
  | CMMSizeCons : ∀ mm0 mm1 mxs,
    cubeFaceExtent (cubeMapFaceZNeg mm1) < cubeFaceOffset (cubeMapFaceXPos mm0) →
      cubeOffsetsSorted (mm0 :: mxs) →
        cubeOffsetsSorted (mm1 :: mm0 :: mxs).

Inductive cubeMipMapListIsSorted : list cubeMipMap → Prop :=
  | CubeOne   : ∀ m, cubeMipMapListIsSorted [m]
  | CubeCons  : ∀ mm0 mm1 mxs,
    cubeMapLevel mm1 = S (cubeMapLevel mm0) →
      cubeMipMapListIsSorted (mm0 :: mxs) →
        cubeMipMapListIsSorted (mm1 :: mm0 :: mxs).

Inductive cubeMipMapList : Set := CubeList {
  cubeMipMaps              : list cubeMipMap;
  cubeMipMapsListSorted    : cubeMipMapListIsSorted cubeMipMaps;
  cubeMipMapsOffsetsSorted : cubeOffsetsSorted cubeMipMaps;
}.

Lemma cubeMipMapsNonEmpty : ∀ (m : cubeMipMapList),
  [] ≠ cubeMipMaps m.
Proof.
  intros m.
  destruct (cubeMipMapsOffsetsSorted m).
  - discriminate.
  - discriminate.
Qed.

Definition cubeMipMapsFirst (m : cubeMipMapList) : cubeMipMap.
Proof.
  assert ([] ≠ cubeMipMaps m) as Hneq by (apply (cubeMipMapsNonEmpty)).
  destruct (cubeMipMaps m) eqn:Hm.
  - contradiction.
  - exact c.
Defined.

Fixpoint cubeMipMapImageDataSizeTotalAux (m : list cubeMipMap) : nat :=
  match m with
  | []        => 0
  | (x :: []) => cubeFaceExtent (cubeMapFaceZNeg x)
  | (x :: xs) => cubeMipMapImageDataSizeTotalAux xs
  end.

Definition cubeMipMapImageDataSizeTotal (m : cubeMipMapList) : nat :=
  cubeMipMapImageDataSizeTotalAux (cubeMipMaps m).

Example cubeFaceXP0 := CubeMapFace 0 8 8 0.
Example cubeFaceXN0 := CubeMapFace 16 8 8 0.
Example cubeFaceYP0 := CubeMapFace 32 8 8 0.
Example cubeFaceYN0 := CubeMapFace 48 8 8 0.
Example cubeFaceZP0 := CubeMapFace 64 8 8 0.
Example cubeFaceZN0 := CubeMapFace 80 8 8 0.

Example cubeMipMap0 := CubeMipMap 1 cubeFaceXP0 cubeFaceXN0 cubeFaceYP0 cubeFaceYN0 cubeFaceZP0 cubeFaceZN0.

Example cubeFaceXP1 := CubeMapFace 96 8 8 0.
Example cubeFaceXN1 := CubeMapFace 112 8 8 0.
Example cubeFaceYP1 := CubeMapFace 128 8 8 0.
Example cubeFaceYN1 := CubeMapFace 144 8 8 0.
Example cubeFaceZP1 := CubeMapFace 160 8 8 0.
Example cubeFaceZN1 := CubeMapFace 176 8 8 0.

Example cubeMipMap1 := CubeMipMap 0 cubeFaceXP1 cubeFaceXN1 cubeFaceYP1 cubeFaceYN1 cubeFaceZP1 cubeFaceZN1.

Example cubeOffsetsSortedExample0 : cubeOffsetsSorted [cubeMipMap0].
Proof.
  apply CMMSizeOne.
  compute; repeat constructor.
  compute; repeat constructor.
  compute; repeat constructor.
  compute; repeat constructor.
  compute; repeat constructor.
Qed.

Example cubeOffsetsSortedExample1 : cubeOffsetsSorted [cubeMipMap1].
Proof.
  apply CMMSizeOne.
  compute; repeat constructor.
  compute; repeat constructor.
  compute; repeat constructor.
  compute; repeat constructor.
  compute; repeat constructor.
Qed.

Example cubeOffsetsSortedExample2 : cubeOffsetsSorted [cubeMipMap0; cubeMipMap1].
Proof.
  apply CMMSizeCons.
  compute; repeat constructor.
  exact cubeOffsetsSortedExample1.
Qed.

Example cubeLevelSortedExample0 : cubeMipMapListIsSorted [cubeMipMap0].
Proof.
  apply CubeOne.
Qed.

Example cubeLevelSortedExample1 : cubeMipMapListIsSorted [cubeMipMap1].
Proof.
  apply CubeOne.
Qed.

Example cubeLevelSortedExample2 : cubeMipMapListIsSorted [cubeMipMap0; cubeMipMap1].
Proof.
  apply CubeCons.
  reflexivity.
  apply CubeOne.
Qed.

