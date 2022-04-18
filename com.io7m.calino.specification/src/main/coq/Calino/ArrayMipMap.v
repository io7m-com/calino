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

Fixpoint arrayMipMapLayerCountForLevel
  (level : nat)
  (m     : list arrayMipMap)
: nat :=
  match m with
  | []        => 0
  | (x :: xs) =>
    match Nat.eq_dec (arrayMipMapLevel (arrayMipMapIndex x)) level with
    | left _  => 1 + (arrayMipMapLayerCountForLevel level xs)
    | right _ => (arrayMipMapLayerCountForLevel level xs)
    end
  end.

Definition arrayMipMapLevels (m : list arrayMipMap) : list nat :=
  nodup Nat.eq_dec (map (λ k, arrayMipMapLevel (arrayMipMapIndex k)) m).

Definition arrayMipMapsHaveSameLayers : (list arrayMipMap) → nat → nat → Prop :=
  λ m level0 level1, 
    In level0 (arrayMipMapLevels m) →
      In level1 (arrayMipMapLevels m) →
        arrayMipMapLayerCountForLevel level0 m = arrayMipMapLayerCountForLevel level1 m.

Inductive arrayMipMapList : Set := ArrayMipMapList {
  arrayMipMaps                : list arrayMipMap;
  arrayMipMapIndicesAreSorted : arrayMipMapIndicesSorted (map arrayMipMapIndex arrayMipMaps);
  arrayMipMapOffsetAreSorted  : arrayMipMapOffsetsSorted arrayMipMaps;
  arrayMipMapSameLayers       : ∀ level0 level1, arrayMipMapsHaveSameLayers arrayMipMaps level0 level1
}.

Inductive arrayMipMapImageSize : Set := ArrayMipMapImageSize {
  ammSizeX      : nat;
  ammSizeY      : nat;
  ammSizeXRange : 1 < ammSizeX;
  ammSizeYRange : 1 < ammSizeY;
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
    match (Nat.ltb_spec0 1 sx, Nat.ltb_spec0 1 sy) with
    | (ReflectT _ xt, ReflectT _ yt) => Some (ArrayMipMapImageSize sx sy xt yt)
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

Example exampleArrayMipMapsIndices := [
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

Example exampleArrayMipMaps := 
  map (λ i, ArrayMipMap i 0 0 0 0) exampleArrayMipMapsIndices.

Example exampleArrayMipMapIndicesSorted : arrayMipMapIndicesSorted exampleArrayMipMapsIndices.
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

Example exampleArrayMipMapsHaveSameLayers0 : arrayMipMapLayerCountForLevel 0 exampleArrayMipMaps = 3.
Proof. reflexivity. Qed.
Example exampleArrayMipMapsHaveSameLayers1 : arrayMipMapLayerCountForLevel 1 exampleArrayMipMaps = 3.
Proof. reflexivity. Qed.
Example exampleArrayMipMapsHaveSameLayers2 : arrayMipMapLayerCountForLevel 2 exampleArrayMipMaps = 3.
Proof. reflexivity. Qed.

Example exampleArrayMipMapsLevel : ∀ n, In n (arrayMipMapLevels exampleArrayMipMaps) →
  n = 0 \/ n = 1 \/ n = 2.
Proof.
  intros n.
  simpl.
  intros H.
  destruct H; auto.
  destruct H; auto.
  destruct H; auto.
  contradiction H.
Qed.

Example exampleArrayMipMapsHaveSameLayers : ∀ level0 level1, arrayMipMapsHaveSameLayers exampleArrayMipMaps level0 level1.
Proof.
  intros level0 level1.
  unfold arrayMipMapsHaveSameLayers.
  intros H_In0 H_In1.
  assert (level0 = 0 ∨ level0 = 1 ∨ level0 = 2) as Hl0 by (apply (exampleArrayMipMapsLevel level0 H_In0)).
  assert (level1 = 0 ∨ level1 = 1 ∨ level1 = 2) as Hl1 by (apply (exampleArrayMipMapsLevel level1 H_In1)).
  destruct Hl0 as [Heq0|Heq0]. {
    destruct Hl1 as [Heq1|Heq1]. {
      rewrite Heq0.
      rewrite Heq1.
      reflexivity.
    }
    destruct Heq1 as [Heq1_0|Heq1_0]. {
      rewrite Heq0.
      rewrite Heq1_0.
      reflexivity.
    }
    rewrite Heq0.
    rewrite Heq1_0.
    reflexivity.
  }
  destruct Heq0 as [Heq0_0|Heq0_0]. {
    rewrite Heq0_0.
    destruct Hl1 as [Heq1|Heq1]. {
      rewrite Heq1.
      reflexivity.
    }
    destruct Heq1 as [Heq1_0|Heq1_0]. {
      rewrite Heq1_0.
      reflexivity.
    }
    rewrite Heq1_0.
    reflexivity.
  }
  destruct Hl1 as [Heq1|Heq1]. {
    rewrite Heq0_0.
    rewrite Heq1.
    reflexivity.
  }
  destruct Heq1 as [Heq1_0|Heq1_0]. {
    rewrite Heq0_0.
    rewrite Heq1_0.
    reflexivity.
  }
  rewrite Heq0_0.
  rewrite Heq1_0.
  reflexivity.
Qed.
