Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.ImageSize.

Import ListNotations.

Inductive arrayMipMapIndexT : Set := ArrayMipMapIndex {
  arrayMipMapLevel : nat;
  arrayMipMapLayer : nat;
}.

Inductive arrayMipMapIndexOrd : arrayMipMapIndexT → arrayMipMapIndexT → Prop :=
  | AMMIOrdEq : ∀ i0 i1,
    i0 = i1 → arrayMipMapIndexOrd i0 i1
  | AMMIOrdLevelEq : ∀ i0 i1,
    arrayMipMapLevel i0 = arrayMipMapLevel i1 →
      arrayMipMapLayer i0 < arrayMipMapLayer i1 →
        arrayMipMapIndexOrd i0 i1
  | AMIIOrdLevelLt : ∀ i0 i1,
    arrayMipMapLevel i1 < arrayMipMapLevel i0 →
      arrayMipMapIndexOrd i0 i1.

Inductive arrayMipMapIndicesSorted : list arrayMipMapIndexT → Prop :=
  | AMMIOne  : ∀ m, arrayMipMapIndicesSorted [m]
  | AMMICons : ∀ mmx mmy mxs,
    arrayMipMapIndexOrd mmx mmy →
      arrayMipMapIndicesSorted (mmy :: mxs) →
        arrayMipMapIndicesSorted (mmx :: mmy :: mxs).

Example exampleArrayMipMapIndicesSorted : arrayMipMapIndicesSorted [
  (ArrayMipMapIndex 2 0);
  (ArrayMipMapIndex 2 1);
  (ArrayMipMapIndex 2 2);
  (ArrayMipMapIndex 1 0);
  (ArrayMipMapIndex 1 1);
  (ArrayMipMapIndex 1 2);
  (ArrayMipMapIndex 0 0);
  (ArrayMipMapIndex 0 1);
  (ArrayMipMapIndex 0 2)
].
Proof.
  apply AMMICons. { apply AMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply AMMICons. { apply AMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply AMMICons. { apply AMIIOrdLevelLt. compute; constructor. }
  apply AMMICons. { apply AMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply AMMICons. { apply AMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply AMMICons. { apply AMIIOrdLevelLt. compute; constructor. }
  apply AMMICons. { apply AMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply AMMICons. { apply AMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply AMMIOne.
Qed.

Inductive arrayMipMap : Set := ArrayMipMap {
  arrayMipMapIndex            : arrayMipMapIndexT;
  arrayMipMapOffset           : nat;
  arrayMipMapSizeCompressed   : nat;
  arrayMipMapSizeUncompressed : nat;
  arrayMipMapCRC32            : nat
}.

Inductive arrayMipMapOffsetsSorted : list arrayMipMap → Prop :=
  | AMMSizeOne  : ∀ m, arrayMipMapOffsetsSorted [m]
  | AMMSizeCons : ∀ mm0 mm1 mxs,
    ((arrayMipMapOffset mm1) + (arrayMipMapSizeCompressed mm1)) < (arrayMipMapOffset mm0) →
      arrayMipMapOffsetsSorted (mm0 :: mxs) →
        arrayMipMapOffsetsSorted (mm1 :: mm0 :: mxs).

Inductive arrayMipMapList : Set := ArrayMipMapList {
  arrayMipMaps                : list arrayMipMap;
  arrayMipMapIndicesAreSorted : arrayMipMapIndicesSorted (map arrayMipMapIndex arrayMipMaps);
  arrayMipMapOffsetAreSorted  : arrayMipMapOffsetsSorted arrayMipMaps;
}.

Inductive arrayMipMapImageSize : Set := ArrayMipMapImageSize {
  ammSizeX           : nat;
  ammSizeY           : nat;
  ammSizeLayers      : nat;
  ammSizeXRange      : 1 < ammSizeX;
  ammSizeYRange      : 1 < ammSizeY;
  ammSizeLayersRange : 0 < ammSizeLayers;
}.

Lemma arrayMipMapsNonEmpty : ∀ (m : arrayMipMapList),
  [] ≠ arrayMipMaps m.
Proof.
  intros m.
  destruct (arrayMipMapOffsetAreSorted m).
  - discriminate.
  - discriminate.
Qed.

Definition arrayMipMapFirst (m : arrayMipMapList) : arrayMipMap.
Proof.
  assert ([] ≠ arrayMipMaps m) as Hneq by (apply (arrayMipMapsNonEmpty)).
  destruct (arrayMipMaps m) eqn:Hm.
  - contradiction.
  - exact a.
Defined.

Lemma lt_neq : ∀ n, 0 ≠ n ↔ 0 < n.
Proof.
  intros n.
  constructor.
  - intro Hneq.
    induction n as [|k].
    -- unfold not in Hneq.
       assert (0 = 0) as Heq by reflexivity.
       contradiction.
    -- apply (Nat.lt_0_succ k).
  - intro Hneq.
    induction n as [|k].
    -- inversion Hneq.
    -- discriminate.
Qed.

Lemma lt_neq_0 : ∀ n, 0 ≠ n → 0 < n.
Proof.
  intros n Hneq.
  rewrite <- lt_neq; trivial.
Qed.

Lemma lt_neq_1 : ∀ n, 0 < n → 0 ≠ n.
Proof.
  intros n Hneq.
  rewrite lt_neq; trivial.
Qed.

Definition arrayMipMapSize
  (level      : nat) 
  (imageSize  : imageSize3D)
  (levelRange : 0 < level)
: option arrayMipMapImageSize :=
  let sx  := (sizeX imageSize) / 2 ^ level  in
  let sy  := (sizeY imageSize) / 2 ^ level  in
  let sa  := (sizeZ imageSize) in
  let sar := lt_neq_0 _ (sizeZnot0 imageSize) in
    match (Nat.ltb_spec0 1 sx, Nat.ltb_spec0 1 sy) with
    | (ReflectT _ xt, ReflectT _ yt) => Some (ArrayMipMapImageSize sx sy sa xt yt sar)
    | (_, _)                         => None
    end.

Fixpoint arrayMipMapImageDataSizeTotalAux (m : list arrayMipMap) : nat :=
  match m with
  | []        => 0
  | (x :: []) => (arrayMipMapOffset x) + (arrayMipMapSizeCompressed x)
  | (x :: xs) => arrayMipMapImageDataSizeTotalAux xs
  end.

Definition arrayMipMapImageDataSizeTotal (m : arrayMipMapList) : nat :=
  arrayMipMapImageDataSizeTotalAux (arrayMipMaps m).

