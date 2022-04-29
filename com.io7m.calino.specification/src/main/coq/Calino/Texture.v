Require Import Coq.Unicode.Utf8_core.

Require Import Calino.CubeMipMap.
Require Import Calino.ArrayMipMap.
Require Import Calino.ImageInfo.
Require Import Calino.MipMap.

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
  | TTexture2D    : texture2d → texture
  | TTextureArray : textureArray → texture
  | TTextureCube  : textureCube → texture.

Definition imageInfoOf (i : texture) : imageInfo :=
  match i with
  | TTexture2D (Texture2D i _ _)       => i
  | TTextureArray (TextureArray i _ _) => i
  | TTextureCube (TextureCube i _ _)   => i
  end.

