Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.
Open Scope char_scope.

Set Mangle Names.

Definition digitOfNat (n : nat) : ascii :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end.

Fixpoint stringOfNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (digitOfNat (n mod 10)) acc in
  match time with
  | 0 => acc'
  | S time' =>
    match n / 10 with
    | 0 => acc'
    | n' => stringOfNatAux time' n' acc'
    end
  end.

Definition stringOfNat (n : nat) : string :=
  stringOfNatAux n n "".
