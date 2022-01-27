Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.ImageSize.

Import ListNotations.

Inductive mipMap : Set := MipMap {
  mipMapLevel            : nat;
  mipMapOffset           : nat;
  mipMapSizeCompressed   : nat;
  mipMapSizeUncompressed : nat;
  mipMapCRC32            : nat
}.

Inductive mipMapListIsSorted : list mipMap → Prop :=
  | MipsOne   : ∀ m, mipMapListIsSorted [m]
  | MipsCons  : ∀ mm0 mm1 mxs,
    mipMapLevel mm1 = S (mipMapLevel mm0) →
      mipMapListIsSorted (mm0 :: mxs) →
        mipMapListIsSorted (mm1 :: mm0 :: mxs).

Inductive mipMapList : Set := MipMapList {
  mipMaps          : list mipMap;
  mipMapListSorted : mipMapListIsSorted mipMaps
}.

Inductive mipMapImageSize : Set := MipMapImageSize {
  mmSizeX      : nat;
  mmSizeY      : nat;
  mmSizeZ      : nat;
  mmSizeXRange : 1 < mmSizeX;
  mmSizeYRange : 1 < mmSizeY;
  mmSizeZRange : 0 < mmSizeZ;
}.

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

Definition mipMapSize 
  (level      : nat) 
  (imageSize  : imageSize3D)
  (levelRange : 0 < level)
: option mipMapImageSize :=
  let sx := (sizeX imageSize) / 2 ^ level in
  let sy := (sizeY imageSize) / 2 ^ level in
    match (Nat.ltb_spec0 1 sx, Nat.ltb_spec0 1 sy) with
    | (ReflectT _ xt, ReflectT _ yt) =>
      let z  := sizeZ imageSize in
      let zn := lt_neq_0 z (sizeZnot0 imageSize) in
        Some (MipMapImageSize sx sy z xt yt zn)
    | (_, _) => 
      None
    end.

