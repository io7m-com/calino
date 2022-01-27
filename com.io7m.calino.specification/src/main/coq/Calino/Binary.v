Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Init.Byte.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Basics.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.Metadata.
Require Import Calino.MipMap.
Require Import Calino.ImageInfo.
Require Import Calino.Divisible8.
Require Import Calino.StringUtility.
Require Import Calino.Descriptor.
Require Import Calino.ChannelDescription.
Require Import Calino.ChannelSemantic.
Require Import Calino.ChannelType.
Require Import Calino.Compression.
Require Import Calino.SuperCompression.
Require Import Calino.ColorSpace.
Require Import Calino.Flag.
Require Import Calino.ByteOrder.
Require Import Calino.CoordinateSystem.
Require Import Calino.ImageSize.

Import ListNotations.

Open Scope program_scope.
Open Scope string_scope.

Set Mangle Names.

Inductive streamE : Set :=
  | Vu64 : nat → streamE
  | Vu32 : nat → streamE
  | Vu8  : nat → streamE.

Definition streamSize (s : streamE) : nat :=
  match s with
  | Vu64 _ => 8
  | Vu32 _ => 4
  | Vu8  _ => 1
  end.

Section binaryExpressions.

  Local Unset Elimination Schemes.

  Inductive binaryExp : Set :=
    | BiU32     : nat → binaryExp
    | BiU64     : nat → binaryExp
    | BiBytes   : list byte → binaryExp
    | BiUTF8    : list byte → binaryExp
    | BiArray   : list binaryExp → binaryExp
    | BiReserve : nat → binaryExp
    | BiRecord  : list (string * binaryExp) → binaryExp.

  Section binaryExp_rect.
    Variable P             : binaryExp → Type.
    Variable P_list        : list binaryExp → Type.
    Hypothesis P_nil       : P_list [].
    Hypothesis P_cons      : ∀ x xs, P x → P_list xs → P_list (x :: xs).
    Hypothesis P_BiU32     : ∀ x, P (BiU32 x).
    Hypothesis P_BiU64     : ∀ x, P (BiU64 x).
    Hypothesis P_BiBytes   : ∀ bs, P (BiBytes bs).
    Hypothesis P_BiUTF8    : ∀ bs, P (BiUTF8 bs).
    Hypothesis P_BiArray   : ∀ bs, P_list bs → P (BiArray bs).
    Hypothesis P_BiReserve : ∀ x, P (BiReserve x).
    Hypothesis P_BiRecord  : ∀ fs, P_list (map snd fs) → P (BiRecord fs).

    Fixpoint binaryExp_rect (b : binaryExp) : P b :=
      let
        fix expForAll (xs : list binaryExp) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (binaryExp_rect y) (expForAll ys)
          end
      in let
        fix forAllSnd (fs : list (string * binaryExp)) : P_list (map snd fs) :=
          match fs as rf return P_list (map snd rf) with
          | []             => @P_nil
          | ((_, y) :: ys) => @P_cons y (map snd ys) (binaryExp_rect y) (forAllSnd ys)
          end
      in
        match b with
        | BiU32 c     => P_BiU32 c
        | BiU64 c     => P_BiU64 c
        | BiBytes bs  => P_BiBytes bs
        | BiUTF8 bs   => P_BiUTF8 bs
        | BiArray es  => P_BiArray es (expForAll es)
        | BiReserve c => P_BiReserve c
        | BiRecord fs => P_BiRecord fs (forAllSnd fs)
        end.

  End binaryExp_rect.

  Section binaryExp_ind.
    Variable P             : binaryExp → Prop.
    Hypothesis P_BiU32     : ∀ x, P (BiU32 x).
    Hypothesis P_BiU64     : ∀ x, P (BiU64 x).
    Hypothesis P_BiBytes   : ∀ bs, P (BiBytes bs).
    Hypothesis P_BiUTF8    : ∀ bs, P (BiUTF8 bs).
    Hypothesis P_BiArray   : ∀ bs, Forall P bs → P (BiArray bs).
    Hypothesis P_BiReserve : ∀ x, P (BiReserve x).
    Hypothesis P_BiRecord  : ∀ fs, Forall P (map snd fs) → P (BiRecord fs).

    Definition binaryExp_ind (b : binaryExp) : P b :=
      binaryExp_rect 
        P
        (List.Forall P)
        (List.Forall_nil _)
        (λ x xs Px Pxs, List.Forall_cons _ Px Pxs)
        P_BiU32
        P_BiU64
        P_BiBytes
        P_BiUTF8
        P_BiArray
        P_BiReserve
        P_BiRecord
        b.

  End binaryExp_ind.
End binaryExpressions.

Definition sizeMultipleOf (size q : nat) (Hnz : 0 ≠ q) : nat :=
  let r := size / q in
    match Nat.ltb_spec0 r q with
    | ReflectT _ _ => (r + 1) * q
    | ReflectF _ _ => r * q
    end.

Lemma p0not4 : 0 ≠ 4.
Proof. discriminate. Qed.
Lemma p0not16 : 0 ≠ 16.
Proof. discriminate. Qed.

Fixpoint binarySize (b : binaryExp) : nat :=
  match b with
  | BiU32 _     => 4
  | BiU64 _     => 8
  | BiBytes s   => 4 + sizeMultipleOf (length s) 4 p0not4
  | BiUTF8 s    => 4 + sizeMultipleOf (length s) 4 p0not4
  | BiArray f   => 4 + fold_right plus 0 (map binarySize f)
  | BiReserve s => sizeMultipleOf s 4 p0not4
  | BiRecord f  => fold_right plus 0 (map (binarySize ∘ snd) f)
  end.

Definition binaryEvalPaddedBytes 
  (b     : list byte) 
  (align : nat) 
  (Hneq  : 0 ≠ align) 
: list streamE :=
  let v8 := map (Vu8 ∘ Byte.to_nat) b in
  let vm := length v8 mod align in
    match (Nat.eqb_spec 0 vm) with
    | ReflectT _ _ => v8
    | ReflectF _ _ => v8 ++ (repeat (Vu8 0) vm) 
    end.

Fixpoint binaryEval (b : binaryExp) : list streamE :=
  match b with
  | BiU32 k     => [Vu32 k]
  | BiU64 k     => [Vu64 k]
  | BiBytes s   => (Vu32 (length s)) :: (binaryEvalPaddedBytes s 4 p0not4)
  | BiUTF8 s    => (Vu32 (length s)) :: (binaryEvalPaddedBytes s 4 p0not4)
  | BiArray f   => fold_right (@app streamE) [] (map binaryEval f)
  | BiReserve s => repeat (Vu8 0) (sizeMultipleOf s 4 p0not4)
  | BiRecord f  => fold_right (@app streamE) [] (map (binaryEval ∘ snd) f)
  end.

Definition binarySizePadded16 (b : binaryExp) : nat :=
  sizeMultipleOf (binarySize b) 16 p0not16.

Definition utf8 (s : string) : binaryExp :=
  BiUTF8 (list_byte_of_string s).

Definition u32 := BiU32.
Definition u64 := BiU64.

Definition binaryExpMipMap (m : mipMap) : binaryExp := BiRecord [
  ("mipMapLevel",            u32 (mipMapLevel m));
  ("mipMapDataOffset",       u64 (mipMapOffset m));
  ("mipMapSizeUncompressed", u64 (mipMapSizeUncompressed m));
  ("mipMapSizeCompressed",   u64 (mipMapSizeCompressed m));
  ("mipMapCRC32",            u32 (mipMapCRC32 m))
].

Definition binaryExpMipMaps (m : mipMapList) : binaryExp :=
  BiArray (map binaryExpMipMap (mipMaps m)).

Definition binaryExpCompression (c : compressionMethod) : binaryExp := BiRecord [
  ("descriptor",        utf8 (descriptorOf c));
  ("sectionIdentifier", u64 (compressionSectionIdentifier c));
  ("blockSizeX",        u32 (compressionBlockSizeX c));
  ("blockSizeY",        u32 (compressionBlockSizeY c));
  ("blockAlignment",    u32 (compressionBlockAlignment c))
].

Definition binaryExpSuperCompression (c : superCompressionMethod) : binaryExp := BiRecord [
  ("descriptor",        utf8 (descriptorOf c));
  ("sectionIdentifier", u64 (superCompressionSectionIdentifier c))
].

Definition binaryExpImageInfo (i : imageInfo) : binaryExp := BiRecord [
  ("sizeX",            u32 (imageSizeX i));
  ("sizeY",            u32 (imageSizeY i));
  ("sizeZ",            u32 (imageSizeZ i));
  ("channelsLayout",   utf8 (descriptorOf (imageChannelsLayout i)));
  ("channelsType",     utf8 (descriptorOf (imageChannelsType i)));
  ("compression",      binaryExpCompression (imageCompressionMethod i));
  ("superCompression", binaryExpSuperCompression (imageSuperCompressionMethod i));
  ("coordinateSystem", utf8 (descriptorOf (imageCoordinateSystem i)));
  ("colorSpace",       utf8 (descriptorOf (imageColorSpace i)));
  ("flags",            BiArray (map (utf8 ∘ descriptorOf) (imageFlagSet i)));
  ("byteOrder",        utf8 (descriptorOf (imageByteOrder i)))
].

Definition binaryExpFileHeader : binaryExp := BiRecord [
  ("id",           u64 0x89434C4E0D0A1A0A);
  ("versionMajor", u32 1);
  ("versionMinor", u32 0)
].

Definition binaryExpImageInfoSection (i : imageInfo) : binaryExp := BiRecord [
  ("id",   u64 0x434C4E49494E464F);
  ("size", u64 (binarySizePadded16 (binaryExpImageInfo i)));
  ("data", binaryExpImageInfo i)
].

Definition binaryExpMetadataValue (m : metadataValue) : binaryExp := BiRecord [
  ("key",   utf8 (mKey m));
  ("value", utf8 (mValue m))
].

Definition binaryExpMetadata (m : metadata) : binaryExp :=
  BiArray (map binaryExpMetadataValue (mValues m)).

Definition binaryExpMetadataSection (m : metadata) : binaryExp := BiRecord [
  ("id",   u64 0x434C4E49494E464F);
  ("size", u64 (binarySizePadded16 (binaryExpMetadata m)));
  ("data", binaryExpMetadata m)
].

Definition binaryEndSection : binaryExp := BiRecord [
  ("id",   u64 0x434c4e5f454e4421);
  ("size", u64 0)
].

Lemma sizeMultipleOfMod : ∀ s q (Hneq : 0 ≠ q), (sizeMultipleOf s q Hneq) mod q = 0.
Proof.
  intros s q Hneq.
  unfold sizeMultipleOf.
  destruct (Nat.ltb_spec0 (s / q) q) as [Hlt|H1].
  - apply (Nat.mod_mul (s / q + 1) q (Nat.neq_sym _ _ Hneq)).
  - apply (Nat.mod_mul (s / q) q (Nat.neq_sym _ _ Hneq)).
Qed.

Lemma fold_right_add_cons : ∀ x xs,
  x + fold_right plus 0 xs = fold_right plus 0 (x :: xs).
Proof. reflexivity. Qed.

Lemma forall_map_binarySize : ∀ es, 
  Forall (λ b : binaryExp, binarySize b mod 4 = 0) es 
    ↔ Forall (λ n, n mod 4 = 0) (map binarySize es).
Proof.
  intros es.
  induction es.
  constructor.
  - rewrite Forall_map.
    intros H. trivial.
  - rewrite Forall_map.
    intros H. trivial.
  - rewrite Forall_map.
    constructor.
    intros H; trivial.
    intros H; trivial.
Qed.

Theorem binarySizeMultiple4 : ∀ b, binarySize (b) mod 4 = 0.
Proof.
  intros b.
  induction b as [Hbu32|Hbu64|Hbbyte|Hbutf|xs HFA|Hbuns|xs HFF] using binaryExp_ind.
  (* U32 values are of size 4 *)
  - reflexivity.
  (* U64 values are of size 8 *)
  - reflexivity.
  (* Byte array values are rounded up to a multiple of 4 and prefixed with 4 *)
  - unfold binarySize.
    remember (sizeMultipleOf (Datatypes.length Hbbyte) 4 p0not4) as size eqn:Heqsize.
    rewrite Nat.add_comm.
    rewrite <- (Nat.add_mod_idemp_l size 4 4 (Nat.neq_sym _ _ p0not4)).
    assert (size mod 4 = 0) as Hm0. {
      rewrite Heqsize.
      apply (sizeMultipleOfMod (Datatypes.length Hbbyte) 4 (p0not4)).
    }
    rewrite Hm0.
    reflexivity.
  (* UTF-8 values are rounded up to a multiple of 4 and prefixed with 4 *)
  - unfold binarySize.
    remember (sizeMultipleOf (Datatypes.length Hbutf) 4 p0not4) as size eqn:Heqsize.
    rewrite Nat.add_comm.
    rewrite <- (Nat.add_mod_idemp_l size 4 4 (Nat.neq_sym _ _ p0not4)).
    assert (size mod 4 = 0) as Hm0. {
      rewrite Heqsize.
      apply (sizeMultipleOfMod (Datatypes.length Hbutf) 4 (p0not4)).
    }
    rewrite Hm0.
    reflexivity.
  (* Each element of an array is a multiple of 4, so the entire array is too. *)
  - unfold binarySize.
    fold binarySize.
    induction xs as [|y ys HforAllInd].
    -- reflexivity.
    -- assert (fold_right add 0 (map binarySize (y :: ys)) mod 4 = 0) as HfoldEq. {
         apply (@divisibilityNFoldPlus 4 (map binarySize (y :: ys))).
         discriminate.
         rewrite <- forall_map_binarySize.
         exact HFA.
       }
       rewrite map_cons.
       rewrite map_cons in HfoldEq.
       assert (4 mod 4 = 0) as H4mod40 by (reflexivity).
       assert (0 ≠ 4) as H0n4 by (discriminate).
       apply (divisiblityNAdd 4 (fold_right add 0 (binarySize y :: map binarySize ys)) 4 H0n4 H4mod40 HfoldEq).
  (* Unspecified values are rounded up. *)
  - unfold binarySize.
    rewrite sizeMultipleOfMod.
    reflexivity.
  (* Each element of an record is a multiple of 4, so the entire record is too. *)
  - unfold binarySize.
    fold binarySize.
    induction xs as [|y ys HforAllInd].
    -- reflexivity.
    -- rewrite map_cons.
       rewrite map_cons in HFF.
       rewrite <- fold_right_add_cons.
       apply divisiblityNAdd.
       discriminate.
       apply (Forall_inv HFF).
       apply HforAllInd.
       apply (Forall_inv_tail HFF).
Qed.
