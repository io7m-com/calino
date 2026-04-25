(*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Bool.Bool.

Require Import com.io7m.calino.ImageSize.

Import ListNotations.

Inductive threeDMipMapIndexT : Set := ThreeDMipMapIndex {
  threeDMipMapLevel : nat;
  threeDMipMapDepth : nat;
}.

Inductive threeDMipMapIndexOrd : threeDMipMapIndexT -> threeDMipMapIndexT -> Prop :=
  | ThreeDMMIOrdEq : forall i0 i1,
    i0 = i1 -> threeDMipMapIndexOrd i0 i1
  | ThreeDMMIOrdLevelEq : forall i0 i1,
    threeDMipMapLevel i0 = threeDMipMapLevel i1 ->
      threeDMipMapDepth i0 < threeDMipMapDepth i1 ->
        threeDMipMapIndexOrd i0 i1
  | ThreeDMMIOrdLevelLt : forall i0 i1,
    threeDMipMapLevel i1 < threeDMipMapLevel i0 ->
      threeDMipMapIndexOrd i0 i1.

Inductive threeDMipMapIndicesSorted : list threeDMipMapIndexT -> Prop :=
  | ThreeDMMIOne  : forall m, threeDMipMapIndicesSorted [m]
  | ThreeDMMICons : forall mmx mmy mxs,
    threeDMipMapIndexOrd mmx mmy ->
      threeDMipMapIndicesSorted (mmy :: mxs) ->
        threeDMipMapIndicesSorted (mmx :: mmy :: mxs).

Inductive threeDMipMap : Set := ThreeDMipMap {
  threeDMipMapIndex            : threeDMipMapIndexT;
  threeDMipMapOffset           : nat;
  threeDMipMapSizeCompressed   : nat;
  threeDMipMapSizeUncompressed : nat;
  threeDMipMapCRC32            : nat
}.

Inductive threeDMipMapOffsetsSorted : list threeDMipMap -> Prop :=
  | ThreeDMMSizeOne  : forall m, threeDMipMapOffsetsSorted [m]
  | ThreeDMMSizeCons : forall mm0 mm1 mxs,
    ((threeDMipMapOffset mm1) + (threeDMipMapSizeCompressed mm1)) < (threeDMipMapOffset mm0) ->
      threeDMipMapOffsetsSorted (mm0 :: mxs) ->
        threeDMipMapOffsetsSorted (mm1 :: mm0 :: mxs).

Fixpoint threeDMipMapDepthCountForLevel
  (level : nat)
  (m     : list threeDMipMap)
: nat :=
  match m with
  | []        => 0
  | (x :: xs) =>
    match Nat.eq_dec (threeDMipMapLevel (threeDMipMapIndex x)) level with
    | left _  => 1 + (threeDMipMapDepthCountForLevel level xs)
    | right _ => (threeDMipMapDepthCountForLevel level xs)
    end
  end.

Definition threeDMipMapLevels (m : list threeDMipMap) : list nat :=
  nodup Nat.eq_dec (map (fun k => threeDMipMapLevel (threeDMipMapIndex k)) m).

Definition threeDMipMapsHaveSameDepths : (list threeDMipMap) -> nat -> nat -> Prop :=
  fun m level0 level1 =>
    In level0 (threeDMipMapLevels m) ->
      In level1 (threeDMipMapLevels m) ->
        threeDMipMapDepthCountForLevel level0 m = threeDMipMapDepthCountForLevel level1 m.

Inductive threeDMipMapList : Set := ThreeDMipMapList {
  threeDMipMaps                : list threeDMipMap;
  threeDMipMapIndicesAreSorted : threeDMipMapIndicesSorted (map threeDMipMapIndex threeDMipMaps);
  threeDMipMapOffsetAreSorted  : threeDMipMapOffsetsSorted threeDMipMaps;
  threeDMipMapSameDepths       : forall level0 level1, threeDMipMapsHaveSameDepths threeDMipMaps level0 level1
}.

Inductive threeDMipMapImageSize : Set := ThreeDMipMapImageSize {
  threeDSizeX      : nat;
  threeDSizeY      : nat;
  threeDSizeZ      : nat;
  threeDSizeXRange : 1 < threeDSizeX;
  threeDSizeYRange : 1 < threeDSizeY;
  threeDSizeZRange : 1 < threeDSizeZ;
}.

Lemma threeDMipMapsNonEmpty : forall (m : threeDMipMapList),
  [] <> threeDMipMaps m.
Proof.
  intros m.
  destruct (threeDMipMapOffsetAreSorted m).
  - discriminate.
  - discriminate.
Qed.

Definition threeDMipMapFirst (m : threeDMipMapList) : threeDMipMap.
Proof.
  assert ([] <> threeDMipMaps m) as Hneq by (apply (threeDMipMapsNonEmpty)).
  destruct (threeDMipMaps m) eqn:Hm.
  - contradiction.
  - exact t.
Defined.

Lemma lt_neq : forall n, 0 <> n <-> 0 < n.
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

Lemma lt_neq_0 : forall n, 0 <> n -> 0 < n.
Proof.
  intros n Hneq.
  rewrite <- lt_neq; trivial.
Qed.

Lemma lt_neq_1 : forall n, 0 < n -> 0 <> n.
Proof.
  intros n Hneq.
  rewrite lt_neq; trivial.
Qed.

Definition threeDMipMapSize
  (level      : nat)
  (imageSize  : imageSize3D)
  (levelRange : 0 < level)
: option threeDMipMapImageSize :=
  let sx  := (sizeX imageSize) / 2 ^ level  in
  let sy  := (sizeY imageSize) / 2 ^ level  in
  let sz  := (sizeZ imageSize) / 2 ^ level  in
    match (Nat.ltb_spec0 1 sx, Nat.ltb_spec0 1 sy, Nat.ltb_spec0 1 sz) with
    | (ReflectT _ xt, ReflectT _ yt, ReflectT _ zt) => Some (ThreeDMipMapImageSize sx sy sz xt yt zt)
    | (_, _, _)                                     => None
    end.

Fixpoint threeDMipMapImageDataSizeTotalAux (m : list threeDMipMap) : nat :=
  match m with
  | []        => 0
  | (x :: []) => (threeDMipMapOffset x) + (threeDMipMapSizeCompressed x)
  | (x :: xs) => threeDMipMapImageDataSizeTotalAux xs
  end.

Definition threeDMipMapImageDataSizeTotal (m : threeDMipMapList) : nat :=
  threeDMipMapImageDataSizeTotalAux (threeDMipMaps m).

Example exampleThreeDMipMapsIndices := [
  (ThreeDMipMapIndex 2 0);
  (ThreeDMipMapIndex 2 1);
  (ThreeDMipMapIndex 2 2);
  (ThreeDMipMapIndex 1 0);
  (ThreeDMipMapIndex 1 1);
  (ThreeDMipMapIndex 1 2);
  (ThreeDMipMapIndex 0 0);
  (ThreeDMipMapIndex 0 1);
  (ThreeDMipMapIndex 0 2)
].

Example exampleThreeDMipMaps :=
  map (fun i => ThreeDMipMap i 0 0 0 0) exampleThreeDMipMapsIndices.

Example exampleThreeDMipMapIndicesSorted : threeDMipMapIndicesSorted exampleThreeDMipMapsIndices.
Proof.
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelLt. compute; constructor. }
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelLt. compute; constructor. }
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply ThreeDMMICons. { apply ThreeDMMIOrdLevelEq. reflexivity. compute; constructor. }
  apply ThreeDMMIOne.
Qed.

Example exampleThreeDMipMapsHaveSameDepths0 : threeDMipMapDepthCountForLevel 0 exampleThreeDMipMaps = 3.
Proof. reflexivity. Qed.
Example exampleThreeDMipMapsHaveSameDepths1 : threeDMipMapDepthCountForLevel 1 exampleThreeDMipMaps = 3.
Proof. reflexivity. Qed.
Example exampleThreeDMipMapsHaveSameDepths2 : threeDMipMapDepthCountForLevel 2 exampleThreeDMipMaps = 3.
Proof. reflexivity. Qed.

Example exampleThreeDMipMapsLevel : forall n, In n (threeDMipMapLevels exampleThreeDMipMaps) ->
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

Example exampleThreeDMipMapsHaveSameDepths : forall level0 level1, threeDMipMapsHaveSameDepths exampleThreeDMipMaps level0 level1.
Proof.
  intros level0 level1.
  unfold threeDMipMapsHaveSameDepths.
  intros H_In0 H_In1.
  assert (level0 = 0 \/ level0 = 1 \/ level0 = 2) as Hl0 by (apply (exampleThreeDMipMapsLevel level0 H_In0)).
  assert (level1 = 0 \/ level1 = 1 \/ level1 = 2) as Hl1 by (apply (exampleThreeDMipMapsLevel level1 H_In1)).
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
