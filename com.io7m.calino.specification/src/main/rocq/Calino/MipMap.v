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

Inductive mipMapOffsetsSorted : list mipMap -> Prop :=
  | MMSizeOne  : forall m, mipMapOffsetsSorted [m]
  | MMSizeCons : forall mm0 mm1 mxs,
    ((mipMapOffset mm1) + (mipMapSizeCompressed mm1)) < (mipMapOffset mm0) ->
      mipMapOffsetsSorted (mm0 :: mxs) ->
        mipMapOffsetsSorted (mm1 :: mm0 :: mxs).

Inductive mipMapList : Set := MipMapList {
  mipMaps            : list mipMap;
  mipMapListSorted   : mipMapListIsSorted mipMaps;
  mipMapOffsetSorted : mipMapOffsetsSorted mipMaps;
}.

Inductive mipMapImageSize : Set := MipMapImageSize {
  mmSizeX      : nat;
  mmSizeY      : nat;
  mmSizeXRange : 1 < mmSizeX;
  mmSizeYRange : 1 < mmSizeY;
}.

Lemma mipMapsNonEmpty : forall (m : mipMapList),
  [] <> mipMaps m.
Proof.
  intros m.
  destruct (mipMapListSorted m).
  - discriminate.
  - discriminate.
Qed.

Definition mipMapFirst (m : mipMapList) : mipMap.
Proof.
  assert ([] <> mipMaps m) as Hneq by (apply (mipMapsNonEmpty)).
  destruct (mipMaps m) eqn:Hm.
  - contradiction.
  - exact m0.
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

Definition mipMapSize
  (level      : nat)
  (imageSize  : imageSize3D)
  (levelRange : 0 < level)
: option mipMapImageSize :=
  let sx := (sizeX imageSize) / 2 ^ level in
  let sy := (sizeY imageSize) / 2 ^ level in
    match (Nat.ltb_spec0 1 sx, Nat.ltb_spec0 1 sy) with
    | (ReflectT _ xt, ReflectT _ yt) => Some (MipMapImageSize sx sy xt yt)
    | (_, _)                         => None
    end.

Fixpoint mipMapImageDataSizeTotalAux (m : list mipMap) : nat :=
  match m with
  | []        => 0
  | (x :: []) => (mipMapOffset x) + (mipMapSizeCompressed x)
  | (x :: xs) => mipMapImageDataSizeTotalAux xs
  end.

Definition mipMapImageDataSizeTotal (m : mipMapList) : nat :=
  mipMapImageDataSizeTotalAux (mipMaps m).

