Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.

Require Import Calino.ChannelDescription.
Require Import Calino.ChannelSemantic.
Require Import Calino.ChannelType.

Import ListNotations.

Declare Scope Forall_scope.

Open Scope Forall_scope.

Definition p0n1  : 0 ≠ 1  := O_S 0.
Definition p0n4  : 0 ≠ 4  := O_S 3.
Definition p0n5  : 0 ≠ 5  := O_S 4.
Definition p0n6  : 0 ≠ 6  := O_S 5.
Definition p0n8  : 0 ≠ 8  := O_S 7.
Definition p0n16 : 0 ≠ 16 := O_S 15.
Definition p0n32 : 0 ≠ 32 := O_S 31.
Definition p0n64 : 0 ≠ 64 := O_S 63.

Definition A1 : channelDescription := channelDescriptionMake CSAlpha 1 p0n1.

Definition R5 : channelDescription := channelDescriptionMake CSRed   5 p0n5.
Definition G6 : channelDescription := channelDescriptionMake CSGreen 6 p0n6.
Definition B5 : channelDescription := channelDescriptionMake CSBlue  5 p0n5.

Definition G5 : channelDescription := channelDescriptionMake CSGreen 5 p0n5.

Definition R4 : channelDescription := channelDescriptionMake CSRed   4 p0n4.
Definition G4 : channelDescription := channelDescriptionMake CSGreen 4 p0n4.
Definition B4 : channelDescription := channelDescriptionMake CSBlue  4 p0n4.
Definition A4 : channelDescription := channelDescriptionMake CSAlpha 4 p0n4.

Definition R8 : channelDescription := channelDescriptionMake CSRed   8 p0n8.
Definition G8 : channelDescription := channelDescriptionMake CSGreen 8 p0n8.
Definition B8 : channelDescription := channelDescriptionMake CSBlue  8 p0n8.
Definition A8 : channelDescription := channelDescriptionMake CSAlpha 8 p0n8.

Definition R8_Div8 : channelDescriptionBitsDivisible8 R8 := eq_refl.
Definition G8_Div8 : channelDescriptionBitsDivisible8 G8 := eq_refl.
Definition B8_Div8 : channelDescriptionBitsDivisible8 B8 := eq_refl.
Definition A8_Div8 : channelDescriptionBitsDivisible8 A8 := eq_refl.

Definition R16 : channelDescription := channelDescriptionMake CSRed   16 p0n16.
Definition G16 : channelDescription := channelDescriptionMake CSGreen 16 p0n16.
Definition B16 : channelDescription := channelDescriptionMake CSBlue  16 p0n16.
Definition A16 : channelDescription := channelDescriptionMake CSAlpha 16 p0n16.

Definition R16_Div8 : channelDescriptionBitsDivisible8 R16 := eq_refl.
Definition G16_Div8 : channelDescriptionBitsDivisible8 G16 := eq_refl.
Definition B16_Div8 : channelDescriptionBitsDivisible8 B16 := eq_refl.
Definition A16_Div8 : channelDescriptionBitsDivisible8 A16 := eq_refl.

Definition R32 : channelDescription := channelDescriptionMake CSRed   32 p0n32.
Definition G32 : channelDescription := channelDescriptionMake CSGreen 32 p0n32.
Definition B32 : channelDescription := channelDescriptionMake CSBlue  32 p0n32.
Definition A32 : channelDescription := channelDescriptionMake CSAlpha 32 p0n32.

Definition R32_Div8 : channelDescriptionBitsDivisible8 R32 := eq_refl.
Definition G32_Div8 : channelDescriptionBitsDivisible8 G32 := eq_refl.
Definition B32_Div8 : channelDescriptionBitsDivisible8 B32 := eq_refl.
Definition A32_Div8 : channelDescriptionBitsDivisible8 A32 := eq_refl.

Definition R64 : channelDescription := channelDescriptionMake CSRed   64 p0n64.
Definition G64 : channelDescription := channelDescriptionMake CSGreen 64 p0n64.
Definition B64 : channelDescription := channelDescriptionMake CSBlue  64 p0n64.
Definition A64 : channelDescription := channelDescriptionMake CSAlpha 64 p0n64.

Definition R64_Div8 : channelDescriptionBitsDivisible8 R64 := eq_refl.
Definition G64_Div8 : channelDescriptionBitsDivisible8 G64 := eq_refl.
Definition B64_Div8 : channelDescriptionBitsDivisible8 B64 := eq_refl.
Definition A64_Div8 : channelDescriptionBitsDivisible8 A64 := eq_refl.

(* Packed channels *)

Definition A1_R5_G5_B5_Channels : list channelDescription := [A1; R5; G5; B5].
Definition A1_R5_G5_B5_NonEmpty := nil_cons (x := A1) (l := [R5; G5; B5]).

Definition R4_G4_B4_A4_Channels : list channelDescription := [R4; G4; B4; A4].
Definition R4_G4_B4_A4_NonEmpty := nil_cons (x := R4) (l := [G4; B4; A4]).

Definition R5_G6_B5_Channels : list channelDescription := [R5; G6; B5].
Definition R5_G6_B5_NonEmpty := nil_cons (x := R5) (l := [G6; B5]).

(* 8-bit channels *)

Definition R8_G8_B8_A8_Channels : list channelDescription := [R8; G8; B8; A8].
Definition R8_G8_B8_A8_NonEmpty := nil_cons (x := R8) (l := [G8; B8; A8]).
Definition R8_G8_B8_A8_FDiv8 : Forall channelDescriptionBitsDivisible8 R8_G8_B8_A8_Channels :=
  Forall_cons R8 R8_Div8 
 (Forall_cons G8 G8_Div8 
 (Forall_cons B8 B8_Div8
 (Forall_cons A8 A8_Div8
 (Forall_nil _)))).

Definition R8_G8_B8_Channels : list channelDescription := [R8; G8; B8].
Definition R8_G8_B8_NonEmpty := nil_cons (x := R8) (l := [G8;B8]).
Definition R8_G8_B8_FDiv8 : Forall channelDescriptionBitsDivisible8 R8_G8_B8_Channels :=
  Forall_cons R8 R8_Div8 
 (Forall_cons G8 G8_Div8 
 (Forall_cons B8 B8_Div8 
 (Forall_nil _))).

Definition R8_G8_Channels : list channelDescription := [R8; G8].
Definition R8_G8_NonEmpty := nil_cons (x := R8) (l := [G8]).
Definition R8_G8_FDiv8 : Forall channelDescriptionBitsDivisible8 R8_G8_Channels :=
  Forall_cons R8 R8_Div8 
 (Forall_cons G8 G8_Div8 
 (Forall_nil _)).

Definition R8_Channels : list channelDescription := [R8].
Definition R8_NonEmpty := nil_cons (x := R8) (l := []).
Definition R8_FDiv8 : Forall channelDescriptionBitsDivisible8 R8_Channels :=
  Forall_cons R8 R8_Div8 (Forall_nil _).

(* 16-bit channels *)

Definition R16_G16_B16_A16_Channels : list channelDescription := [R16; G16; B16; A16].
Definition R16_G16_B16_A16_NonEmpty := nil_cons (x := R16) (l := [G16; B16; A16]).
Definition R16_G16_B16_A16_FDiv8 : Forall channelDescriptionBitsDivisible8 R16_G16_B16_A16_Channels :=
  Forall_cons R16 R16_Div8 
 (Forall_cons G16 G16_Div8 
 (Forall_cons B16 B16_Div8
 (Forall_cons A16 A16_Div8
 (Forall_nil _)))).

Definition R16_G16_B16_Channels : list channelDescription := [R16; G16; B16].
Definition R16_G16_B16_NonEmpty := nil_cons (x := R16) (l := [G16;B16]).
Definition R16_G16_B16_FDiv8 : Forall channelDescriptionBitsDivisible8 R16_G16_B16_Channels :=
  Forall_cons R16 R16_Div8 
 (Forall_cons G16 G16_Div8 
 (Forall_cons B16 B16_Div8 
 (Forall_nil _))).

Definition R16_G16_Channels : list channelDescription := [R16; G16].
Definition R16_G16_NonEmpty := nil_cons (x := R16) (l := [G16]).
Definition R16_G16_FDiv8 : Forall channelDescriptionBitsDivisible8 R16_G16_Channels :=
  Forall_cons R16 R16_Div8 
 (Forall_cons G16 G16_Div8 
 (Forall_nil _)).

Definition R16_Channels : list channelDescription := [R16].
Definition R16_NonEmpty := nil_cons (x := R16) (l := []).
Definition R16_FDiv8 : Forall channelDescriptionBitsDivisible8 R16_Channels :=
  Forall_cons R16 R16_Div8 (Forall_nil _).

(* 32-bit channels *)

Definition R32_G32_B32_A32_Channels : list channelDescription := [R32; G32; B32; A32].
Definition R32_G32_B32_A32_NonEmpty := nil_cons (x := R32) (l := [G32; B32; A32]).
Definition R32_G32_B32_A32_FDiv8 : Forall channelDescriptionBitsDivisible8 R32_G32_B32_A32_Channels :=
  Forall_cons R32 R32_Div8 
 (Forall_cons G32 G32_Div8 
 (Forall_cons B32 B32_Div8
 (Forall_cons A32 A32_Div8
 (Forall_nil _)))).

Definition R32_G32_B32_Channels : list channelDescription := [R32; G32; B32].
Definition R32_G32_B32_NonEmpty := nil_cons (x := R32) (l := [G32;B32]).
Definition R32_G32_B32_FDiv8 : Forall channelDescriptionBitsDivisible8 R32_G32_B32_Channels :=
  Forall_cons R32 R32_Div8 
 (Forall_cons G32 G32_Div8 
 (Forall_cons B32 B32_Div8 
 (Forall_nil _))).

Definition R32_G32_Channels : list channelDescription := [R32; G32].
Definition R32_G32_NonEmpty := nil_cons (x := R32) (l := [G32]).
Definition R32_G32_FDiv8 : Forall channelDescriptionBitsDivisible8 R32_G32_Channels :=
  Forall_cons R32 R32_Div8 
 (Forall_cons G32 G32_Div8 
 (Forall_nil _)).

Definition R32_Channels : list channelDescription := [R32].
Definition R32_NonEmpty := nil_cons (x := R32) (l := []).
Definition R32_FDiv8 : Forall channelDescriptionBitsDivisible8 R32_Channels :=
  Forall_cons R32 R32_Div8 (Forall_nil _).

(* 64-bit channels *)

Definition R64_G64_B64_A64_Channels : list channelDescription := [R64; G64; B64; A64].
Definition R64_G64_B64_A64_NonEmpty := nil_cons (x := R64) (l := [G64; B64; A64]).
Definition R64_G64_B64_A64_FDiv8 : Forall channelDescriptionBitsDivisible8 R64_G64_B64_A64_Channels :=
  Forall_cons R64 R64_Div8 
 (Forall_cons G64 G64_Div8 
 (Forall_cons B64 B64_Div8
 (Forall_cons A64 A64_Div8
 (Forall_nil _)))).

Definition R64_G64_B64_Channels : list channelDescription := [R64; G64; B64].
Definition R64_G64_B64_NonEmpty := nil_cons (x := R64) (l := [G64;B64]).
Definition R64_G64_B64_FDiv8 : Forall channelDescriptionBitsDivisible8 R64_G64_B64_Channels :=
  Forall_cons R64 R64_Div8 
 (Forall_cons G64 G64_Div8 
 (Forall_cons B64 B64_Div8 
 (Forall_nil _))).

Definition R64_G64_Channels : list channelDescription := [R64; G64].
Definition R64_G64_NonEmpty := nil_cons (x := R64) (l := [G64]).
Definition R64_G64_FDiv8 : Forall channelDescriptionBitsDivisible8 R64_G64_Channels :=
  Forall_cons R64 R64_Div8 
 (Forall_cons G64 G64_Div8 
 (Forall_nil _)).

Definition R64_Channels : list channelDescription := [R64].
Definition R64_NonEmpty := nil_cons (x := R64) (l := []).
Definition R64_FDiv8 : Forall channelDescriptionBitsDivisible8 R64_Channels :=
  Forall_cons R64 R64_Div8 (Forall_nil _).

(* Layouts *)

Definition Layout_A1_R5_G5_B5 : channelLayoutDescription :=
  ChannelLayoutDescriptionPacked (CLDPMake A1_R5_G5_B5_Channels A1_R5_G5_B5_NonEmpty CLPack16 eq_refl).

Definition Layout_R4_G4_B4_A4 : channelLayoutDescription :=
  ChannelLayoutDescriptionPacked (CLDPMake R4_G4_B4_A4_Channels R4_G4_B4_A4_NonEmpty CLPack16 eq_refl).

Definition Layout_R5_G6_B5 : channelLayoutDescription :=
  ChannelLayoutDescriptionPacked (CLDPMake R5_G6_B5_Channels R5_G6_B5_NonEmpty CLPack16 eq_refl).

Definition Layout_R8_G8_B8_A8 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R8_G8_B8_A8_Channels R8_G8_B8_A8_NonEmpty R8_G8_B8_A8_FDiv8).

Definition Layout_R8_G8_B8 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R8_G8_B8_Channels R8_G8_B8_NonEmpty R8_G8_B8_FDiv8).

Definition Layout_R8_G8 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R8_G8_Channels R8_G8_NonEmpty R8_G8_FDiv8).

Definition Layout_R8 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R8_Channels R8_NonEmpty R8_FDiv8).

Definition Layout_R16_G16_B16_A16 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R16_G16_B16_A16_Channels R16_G16_B16_A16_NonEmpty R16_G16_B16_A16_FDiv8).

Definition Layout_R16_G16_B16 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R16_G16_B16_Channels R16_G16_B16_NonEmpty R16_G16_B16_FDiv8).

Definition Layout_R16_G16 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R16_G16_Channels R16_G16_NonEmpty R16_G16_FDiv8).

Definition Layout_R16 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R16_Channels R16_NonEmpty R16_FDiv8).

Definition Layout_R32_G32_B32_A32 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R32_G32_B32_A32_Channels R32_G32_B32_A32_NonEmpty R32_G32_B32_A32_FDiv8).

Definition Layout_R32_G32_B32 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R32_G32_B32_Channels R32_G32_B32_NonEmpty R32_G32_B32_FDiv8).

Definition Layout_R32_G32 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R32_G32_Channels R32_G32_NonEmpty R32_G32_FDiv8).

Definition Layout_R32 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R32_Channels R32_NonEmpty R32_FDiv8).

Definition Layout_R64_G64_B64_A64 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R64_G64_B64_A64_Channels R64_G64_B64_A64_NonEmpty R64_G64_B64_A64_FDiv8).

Definition Layout_R64_G64_B64 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R64_G64_B64_Channels R64_G64_B64_NonEmpty R64_G64_B64_FDiv8).

Definition Layout_R64_G64 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R64_G64_Channels R64_G64_NonEmpty R64_G64_FDiv8).

Definition Layout_R64 : channelLayoutDescription :=
  ChannelLayoutDescriptionUnpacked (CLDUMake R64_Channels R64_NonEmpty R64_FDiv8).

