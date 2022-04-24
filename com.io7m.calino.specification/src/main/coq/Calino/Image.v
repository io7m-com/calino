Require Import Coq.Unicode.Utf8_core.

Require Import Calino.ArrayMipMap.
Require Import Calino.ImageInfo.
Require Import Calino.MipMap.

Inductive image2d : Set := Image2D {
  i2dInfo    : imageInfo;
  i2dMipMaps : mipMapList;
  i2dSize    : 1 = imageSizeZ i2dInfo
}.

Inductive imageArray : Set := ImageArray {
  iaInfo    : imageInfo;
  iaMipMaps : arrayMipMapList;
  iaSize    : 1 <= imageSizeZ iaInfo
}.

Inductive image : Set :=
  | IImage2D    : image2d → image
  | IImageArray : imageArray → image
  | IImageCube  : imageInfo → image.

Definition imageInfoOf (i : image) : imageInfo :=
  match i with
  | IImage2D (Image2D i _ _)       => i
  | IImageArray (ImageArray i _ _) => i
  | IImageCube i                   => i
  end.
