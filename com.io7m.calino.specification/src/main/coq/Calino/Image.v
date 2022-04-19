Require Import Coq.Unicode.Utf8_core.

Require Import Calino.ArrayMipMap.
Require Import Calino.ImageInfo.
Require Import Calino.MipMap.

Inductive image : Set :=
  | Image2D    : imageInfo → mipMapList → image
  | ImageArray : imageInfo → arrayMipMapList → image
  | ImageCube  : imageInfo → image.

Definition imageInfoOf (i : image) : imageInfo :=
  match i with
  | Image2D i _    => i
  | ImageArray i _ => i
  | ImageCube i    => i
  end.
