Require Import Coq.Unicode.Utf8_core.

Require Import Calino.ImageInfo.
Require Import Calino.MipMap.

Inductive image : Set :=
  | Image2D   : ∀ (i : imageInfo), 
    mipMapList (imageInfoTexelBlockAlignment i) (imageInfoTexelBlockAlignmentNonZero i) → image
  | Image3D   : imageInfo → image
  | ImageCube : imageInfo → image.

Definition imageInfoOf (i : image) : imageInfo :=
  match i with
  | Image2D i _ => i
  | Image3D i   => i
  | ImageCube i => i
  end.

