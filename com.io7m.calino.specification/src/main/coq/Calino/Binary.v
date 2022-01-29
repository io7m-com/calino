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

Definition u8byte : byte → streamE :=
  Vu8 ∘ Byte.to_nat.

Definition streamEIsU8 (e : streamE) : Prop :=
  match e with
  | Vu64 _ => False
  | Vu32 _ => False
  | Vu8  _ => True
  end.

Inductive streamWellFormed : list streamE → Prop :=
  | BEPEmpty : streamWellFormed []
  | BEPVu64 : ∀ k, 
      streamWellFormed [Vu64 k]
  | BEPVu32 : ∀ k, 
      streamWellFormed [Vu32 k]
  | BEPVu8s : ∀ es,
      Forall streamEIsU8 es →
        length (es) mod 4 = 0 →
          streamWellFormed es
  | BEPAppend : ∀ xs ys,
    streamWellFormed xs →
      streamWellFormed ys →
        streamWellFormed (xs ++ ys).

Definition streamElementSize (s : streamE) : nat :=
  match s with
  | Vu64 _ => 8
  | Vu32 _ => 4
  | Vu8  _ => 1
  end.

Definition streamSize (s : list streamE) : nat :=
  fold_right plus 0 (map streamElementSize s).

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

Definition sizeAsMultipleOf (size q : nat) (Hnz : 0 ≠ q) : nat :=
  let r := size / q in
    match Nat.ltb_spec0 r q with
    | ReflectT _ _ => (r + 1) * q
    | ReflectF _ _ => r * q
    end.

Lemma p0not4 : 0 ≠ 4.
Proof. discriminate. Qed.

Lemma p0not16 : 0 ≠ 16.
Proof. discriminate. Qed.

Definition sizeAsMultipleOf4 (size : nat) : nat :=
  sizeAsMultipleOf size 4 p0not4.

Transparent sizeAsMultipleOf4.

Fixpoint binarySize (b : binaryExp) : nat :=
  match b with
  | BiU32 _     => 4
  | BiU64 _     => 8
  | BiBytes s   => 4 + sizeAsMultipleOf4 (length s)
  | BiUTF8 s    => 4 + sizeAsMultipleOf4 (length s)
  | BiArray f   => 4 + fold_right plus 0 (map binarySize f)
  | BiReserve s => sizeAsMultipleOf4 s
  | BiRecord f  => fold_right plus 0 (map (binarySize ∘ snd) f)
  end.

Definition binaryEvalPaddedBytes
  (b     : list byte) 
  (align : nat) 
  (Hneq  : 0 ≠ align) 
: list streamE :=
  let vremaining := length b mod align in
    match vremaining with
    | 0 => map u8byte b
    | _ => map u8byte (b ++ repeat x00 (align - vremaining))
    end.

Fixpoint binaryEval (b : binaryExp) : list streamE :=
  match b with
  | BiU32 k     => [Vu32 k]
  | BiU64 k     => [Vu64 k]
  | BiBytes s   => (Vu32 (length s)) :: (binaryEvalPaddedBytes s 4 p0not4)
  | BiUTF8 s    => (Vu32 (length s)) :: (binaryEvalPaddedBytes s 4 p0not4)
  | BiArray f   => (Vu32 (length f)) :: concat (map binaryEval f)
  | BiReserve s => repeat (Vu8 0) (sizeAsMultipleOf4 s)
  | BiRecord f  => concat (map (binaryEval ∘ snd) f)
  end.

Definition binarySizePadded16 (b : binaryExp) : nat :=
  sizeAsMultipleOf (binarySize b) 16 p0not16.

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
  ("id",   u64 0x434C4E5F4D455441);
  ("size", u64 (binarySizePadded16 (binaryExpMetadata m)));
  ("data", binaryExpMetadata m)
].

Definition binaryEndSection : binaryExp := BiRecord [
  ("id",   u64 0x434c4e5f454e4421);
  ("size", u64 0)
].

Lemma sizeAsMultipleOfMod : ∀ s q (Hneq : 0 ≠ q), (sizeAsMultipleOf s q Hneq) mod q = 0.
Proof.
  intros s q Hneq.
  unfold sizeAsMultipleOf.
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
    unfold sizeAsMultipleOf4.
    remember (sizeAsMultipleOf (Datatypes.length Hbbyte) 4 p0not4) as size eqn:Heqsize.
    rewrite Nat.add_comm.
    rewrite <- (Nat.add_mod_idemp_l size 4 4 (Nat.neq_sym _ _ p0not4)).
    assert (size mod 4 = 0) as Hm0. {
      rewrite Heqsize.
      apply (sizeAsMultipleOfMod (Datatypes.length Hbbyte) 4 (p0not4)).
    }
    rewrite Hm0.
    reflexivity.
  (* UTF-8 values are rounded up to a multiple of 4 and prefixed with 4 *)
  - unfold binarySize.
    unfold sizeAsMultipleOf4.
    remember (sizeAsMultipleOf (Datatypes.length Hbutf) 4 p0not4) as size eqn:Heqsize.
    rewrite Nat.add_comm.
    rewrite <- (Nat.add_mod_idemp_l size 4 4 (Nat.neq_sym _ _ p0not4)).
    assert (size mod 4 = 0) as Hm0. {
      rewrite Heqsize.
      apply (sizeAsMultipleOfMod (Datatypes.length Hbutf) 4 (p0not4)).
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
    unfold sizeAsMultipleOf4.
    rewrite sizeAsMultipleOfMod.
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

Lemma sub_0_lt_ymx : ∀ x y,
  0 <= x → x < y → 0 < y - x.
Proof.
  intros x y Hle Hlt.
  destruct x as [|a].
  - rewrite Nat.sub_0_r.
    exact Hlt.
  - rewrite <- Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r.
    exact Hlt.
Qed.

Lemma mod_sub : ∀ x m,
  0 < m → 0 < m - (x mod m) <= m.
Proof.
  intros x m Hlt.
  constructor.
  - assert (0 <= x mod m < m) as HmRange. {
      apply Nat.mod_bound_pos.
      apply Nat.le_0_l.
      exact Hlt.
    }
    destruct HmRange as [HA HB].
    remember (x mod m) as y.
    apply (sub_0_lt_ymx y m HA HB).
  - assert (x mod m < m) as HmRange. {
      apply Nat.mod_upper_bound.
      apply Nat.neq_sym.
      apply Nat.lt_neq.
      exact Hlt.
    }
    apply Nat.le_sub_l.
Qed.

Lemma mod_opposition : ∀ x a,
  0 ≠ a → x mod a + (a - x mod a) = a.
Proof.
  intros x a Hnz.
  assert (x mod a < a) as Hxma. {
    apply (Nat.mod_upper_bound).
    apply Nat.neq_sym.
    exact Hnz.
  }
  remember (x mod a) as y eqn:Heqy.
  apply Minus.le_plus_minus_r.
  apply (Nat.lt_le_incl _ _ Hxma).
Qed.

Theorem binaryEvalPaddedBytesAligned : ∀ bs a (Hnz : 0 ≠ a),
  length (binaryEvalPaddedBytes bs a Hnz) mod a = 0.
Proof.
  intros bs a Hnz.
  unfold binaryEvalPaddedBytes.
  destruct (Datatypes.length bs mod a) eqn:Hlen.
  - rewrite map_length.
    exact Hlen.
  - rewrite map_length.
    rewrite app_length.
    rewrite repeat_length.
    rewrite <- Hlen.
    remember (Datatypes.length bs) as x.
    rewrite <- (Nat.add_mod_idemp_l x (a - x mod a) a).
    assert ((x mod a + (a - x mod a)) = a) as Heqa. {
      rewrite (mod_opposition x a Hnz).
      reflexivity.
    }
    rewrite Heqa.
    apply Nat.mod_same.
    apply Nat.neq_sym; exact Hnz.
    apply Nat.neq_sym; exact Hnz.
Qed.

Lemma repeat_eq : ∀ (A : Type) (P : A → Prop) (n : nat) (x : A),
  Forall (eq x) (repeat x n).
Proof.
  intros A P n x.
  induction n as [|m Hm].
  - constructor.
  - simpl.
    constructor.
    reflexivity.
    exact Hm.
Qed.

Lemma Forall_implies : ∀ (A : Type) (P : A → Prop) (Q : A → Prop) (xs : list A) (H : ∀ x, P x → Q x), 
  Forall P xs → Forall Q xs.
Proof.
  intros A P Q xs Ht HforAll.
  induction HforAll as [|y ys Hpy HfaP HfaQ].
  - constructor.
  - constructor.
    apply (Ht y Hpy).
    exact HfaQ.
Qed.

Theorem binaryEvalPaddedBytesU8 : ∀ bs a (Hnz : 0 ≠ a),
  Forall streamEIsU8 (binaryEvalPaddedBytes bs a Hnz).
Proof.
  intros bs a Hnz.
  unfold binaryEvalPaddedBytes.
  destruct (Datatypes.length bs mod a) as [|HB].
  - rewrite Forall_map.
    induction bs as [|r rs Hrs].
    -- constructor.
    -- constructor.
       reflexivity.
       exact Hrs.
  - rewrite map_app.
    assert (Forall streamEIsU8 (map u8byte bs)) as Hmap. {
      rewrite Forall_map.
      induction bs as [|r rs Hrs].
      - constructor.
      - constructor.
        reflexivity.
        exact Hrs.
    }
    assert (Forall streamEIsU8 (map u8byte (repeat "000"%byte (a - S HB)))) as HmapR. {
      rewrite Forall_map.
      assert (Forall (eq "000"%byte) (repeat "000"%byte (a - S HB))) as Hfeq
        by (apply (repeat_eq byte (λ _ : byte, True) (a - S HB) "000"%byte)).
      simpl.
      apply (@Forall_implies byte (eq "000"%byte) (λ _ : byte, True) (repeat "000"%byte (a - S HB))). {
        intros. exact I.
      }
      exact Hfeq.
    }
    apply Forall_app.
    constructor.
    exact Hmap.
    exact HmapR.
Qed.

Lemma app_cons : ∀ (A : Type) (x : A) (xs : list A),
  x :: xs = app (cons x nil) xs.
Proof.
  intros A x xs.
  reflexivity.
Qed.

Theorem binaryEvalStreamsWellFormed : ∀ b,
  streamWellFormed (binaryEval b).
Proof.
  intros b.
  induction b as [a0|a1|a2|a3|a4 Hfa|a5|a6 Hfa].
  (* U32 *)
  - apply BEPVu32.
  (* U64 *)
  - apply BEPVu64.
  (* Bytes *)
  - unfold binaryEval.
    rewrite app_cons.
    apply BEPAppend.
    apply BEPVu32.
    assert (length (binaryEvalPaddedBytes a2 4 p0not4) mod 4 = 0) as Hlm
      by (apply (binaryEvalPaddedBytesAligned)).
    apply BEPVu8s.
    apply binaryEvalPaddedBytesU8.
    exact Hlm.
  (* UTF-8 *)
  - unfold binaryEval.
    rewrite app_cons.
    apply BEPAppend.
    apply BEPVu32.
    assert (length (binaryEvalPaddedBytes a3 4 p0not4) mod 4 = 0) as Hlm
      by (apply (binaryEvalPaddedBytesAligned)).
    assert (Forall streamEIsU8 (binaryEvalPaddedBytes a3 4 p0not4)) as Hu8
      by (apply (binaryEvalPaddedBytesU8)).
    apply (BEPVu8s _ Hu8 Hlm).
  (* Array *)
  - simpl.
    rewrite app_cons.
    apply BEPAppend.
    apply BEPVu32.
    induction a4 as [|q qs IHqs].
    -- constructor.
    -- assert (streamWellFormed (concat (map binaryEval qs))) as HqsWF
         by (apply (IHqs (Forall_inv_tail Hfa))).
       assert (streamWellFormed (binaryEval q)) as HqWF
         by (apply (Forall_inv Hfa)).
       simpl.
       apply BEPAppend.
       exact HqWF.
       exact HqsWF.
  (* Reserve *)
  - simpl.
    unfold sizeAsMultipleOf4.
    remember (sizeAsMultipleOf a5 4 p0not4) as size eqn:Heqsize.
    assert (size mod 4 = 0) as Heqm. {
      rewrite Heqsize.
      apply (sizeAsMultipleOfMod).
    }
    assert ((Vu8 ∘ Byte.to_nat) "000"%byte = (Vu8 0)) as HbyteEq by reflexivity.
    apply BEPVu8s.
    assert (Forall (eq (Vu8 0)) (repeat (Vu8 0) size)) as Hfeq
      by (apply (@repeat_eq streamE streamEIsU8 size (Vu8 0))).
    apply (@Forall_implies streamE (eq (Vu8 0)) streamEIsU8 (repeat (Vu8 0) size)). {
      intros x Hxeq.
      unfold streamEIsU8.
      rewrite <- Hxeq.
      exact I.
    }
    exact Hfeq.
    rewrite repeat_length.
    exact Heqm.
  (* Record *)
  - simpl.
    induction a6 as [|q qs IHqs].
    -- constructor.
    -- assert (Forall (λ b : binaryExp, streamWellFormed (binaryEval b)) (map snd qs)) as Hfqs. {
         apply (@Forall_inv_tail binaryExp (λ b : binaryExp, streamWellFormed (binaryEval b)) (snd q) (map snd qs)). {
           assert ((map snd (q :: qs)) = (snd q :: map snd qs)) as Hmc by reflexivity.
           rewrite <- Hmc.
           exact Hfa.
         }
       }
       assert (streamWellFormed (concat (map (binaryEval ∘ snd) qs))) as Hconqs by (apply (IHqs Hfqs)).
       rewrite map_cons.
       rewrite concat_cons.
       apply BEPAppend.
       rewrite map_cons in Hfa.
       apply (Forall_inv Hfa).
       exact Hconqs.
Qed.

Unset Mangle Names.

Lemma fold_right_1_length : ∀ xs,
  Forall (eq 1) xs → fold_right add 0 xs = length xs.
Proof.
  intros xs Hfa.
  induction xs as [|y ys IHxs].
  - reflexivity.
  - rewrite <- fold_right_add_cons.
    assert (length (y :: ys) = 1 + length (ys)) as HlenYs by reflexivity.
    rewrite HlenYs.
    assert (1 = y) as Hy1 by (apply (Forall_inv Hfa)).
    rewrite <- Hy1.
    f_equal.
    apply IHxs.
    apply (Forall_inv_tail Hfa).
Qed.

Theorem fold_right_add_app : ∀ xs ys,
  fold_right add 0 xs + fold_right add 0 ys = fold_right add 0 (xs ++ ys).
Proof.
  intros xs ys.
  rewrite fold_right_app.
  generalize dependent ys.
  induction xs as [|q qs IHqs].
  - reflexivity.
  - intros ys.
    simpl.
    rewrite <- (IHqs ys).
    rewrite Nat.add_assoc.
    reflexivity.
Qed.

Theorem streamSizeApp : ∀ xs ys,
  streamSize xs + streamSize ys = streamSize (xs ++ ys).
Proof.
  intros xs ys.
  unfold streamSize.
  rewrite map_app.
  rewrite fold_right_add_app.
  reflexivity.
Qed.

Theorem streamsWellFormedDivisible4 : ∀ es,
  streamWellFormed es → streamSize es mod 4 = 0.
Proof.
  intros es Hwf.
  induction Hwf as [|H1|H2|es Hfa Hsize|xs ys Hxswf Hxsize Hyswf Hysize].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold streamSize.
    assert (Forall (λ e, 1 = streamElementSize e) es) as HFaSize. { 
      apply (@Forall_implies streamE streamEIsU8 (λ e : streamE, 1 = streamElementSize e) es). {
        intros x His.
        destruct x as [u64|u32|u8].
        - contradiction.
        - contradiction.
        - reflexivity.
      }
      exact Hfa.
    }
    assert (Forall (eq 1) (map streamElementSize es)) as Hall1. {
      apply (@Forall_map _ _ _ _ es).
      exact HFaSize.
    }
    assert (fold_right add 0 (map streamElementSize es) = length es) as HlenEq. {
      assert (length es = length (map streamElementSize es)) as HmapLen. {
        rewrite map_length.
        reflexivity.
      }
      rewrite HmapLen.
      apply (fold_right_1_length (map streamElementSize es) Hall1).
    }
    rewrite HlenEq.
    exact Hsize.
  - rewrite <- streamSizeApp.
    apply divisiblityNAdd.
    discriminate.
    exact Hxsize.
    exact Hysize.
Qed.

