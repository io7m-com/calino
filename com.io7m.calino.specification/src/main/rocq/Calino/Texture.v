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

Require Import com.io7m.calino.CubeMipMap.
Require Import com.io7m.calino.ArrayMipMap.
Require Import com.io7m.calino.ImageInfo.
Require Import com.io7m.calino.MipMap.

Inductive texture2d : Set := Texture2D {
  i2dInfo    : imageInfo;
  i2dMipMaps : mipMapList;
  i2dSize    : 1 = imageSizeZ i2dInfo
}.

Inductive textureArray : Set := TextureArray {
  iaInfo    : imageInfo;
  iaMipMaps : arrayMipMapList;
  iaSize    : 1 <= imageSizeZ iaInfo
}.

Inductive textureCube : Set := TextureCube {
  icubeInfo    : imageInfo;
  icubeMipMaps : cubeMipMapList;
  icubeSize    : 1 = imageSizeZ icubeInfo
}.

Inductive texture : Set :=
  | TTexture2D    : texture2d -> texture
  | TTextureArray : textureArray -> texture
  | TTextureCube  : textureCube -> texture.

Definition imageInfoOf (i : texture) : imageInfo :=
  match i with
  | TTexture2D (Texture2D i _ _)       => i
  | TTextureArray (TextureArray i _ _) => i
  | TTextureCube (TextureCube i _ _)   => i
  end.
