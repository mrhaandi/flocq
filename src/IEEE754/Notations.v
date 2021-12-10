From Coq Require Import ZArith SpecFloat.
Require Import Core BinarySingleNaN Binary.

Section Extra_ops.
(* This Section is copied from (portions of) CompCert.lib.IEEE754_extra.v,
 which is LGPL licensed.  In any case, this IEEE754_extra file should really
 be part of Flocq.
*)

(** [prec] is the number of bits of the mantissa including the implicit one.
    [emax] is the exponent of the infinities.
    Typically p=24 and emax = 128 in single precision. *)

Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.
Hypothesis Hmax : (prec < emax)%Z.

(** Always rounds toward zero. *)
Definition ZofB (f: binary_float prec emax): option Z :=
  match f with
    | B754_finite _ _ s m (Zpos e) _ => Some (cond_Zopp s (Zpos m) * Z.pow_pos radix2 e)%Z
    | B754_finite _ _ s m 0 _ => Some (cond_Zopp s (Zpos m))
    | B754_finite _ _ s m (Zneg e) _ => Some (cond_Zopp s (Zpos m / Z.pow_pos radix2 e))%Z
    | B754_zero _ _ _ => Some 0%Z
    | _ => None
  end.

Definition BofZ (n: Z) : binary_float prec emax :=
  binary_normalize prec emax prec_gt_0_ Hmax mode_NE n 0 false.

Fixpoint pos_pow (x y: positive) : positive :=
  match y with
  | xH => x
  | xO y => Pos.square (pos_pow x y)
  | xI y => Pos.mul x (Pos.square (pos_pow x y))
  end.

Program Definition Bparse (base: positive) (m: positive) (e: Z): binary_float prec emax :=
  match e with
  | Z0 =>
     BofZ (Zpos m)
  | Zpos p =>
     if (e * Z.log2 (Zpos base) <? emax)%Z
     then BofZ (Zpos m * Zpos (pos_pow base p))
     else B754_infinity _ _ false
  | Zneg p =>
     if (e * Z.log2 (Zpos base) + Z.log2_up (Zpos m) <? emin)%Z
     then B754_zero _ _ false
     else BSN2B' prec emax (SF2B _ (proj1 (Bdiv_correct_aux prec emax _ _ mode_NE
                                     false m Z0 false (pos_pow base p) Z0))) _
  end.
Next Obligation.
destruct Bdiv_correct_aux as [H1 H2].
rewrite is_nan_SF2B.
clear H1.
destruct SFdiv_core_binary as [[mz ez] lz].
destruct Rlt_bool.
destruct H2 as [_ [H _]].
now destruct BSN.binary_round_aux.
simpl in H2.
rewrite H2.
apply is_nan_binary_overflow.
Qed.

End Extra_ops.

Module Type BINARY_FLOAT_TO_NUMBER.
 (* This module converts decimal number representations
  of the form [+/-]DDD.DDDDDDDe[+/-]DDD,
  where the sign is optional, the exponent sign is optional, the
  entire exponent is optional, and the decimal-point and fractional part are optional,
  to and from Flocq's IEEE_754 floating point format in any size of mantissa and exponent
  (subject to the restrictions 0<prec, prec<emax).
*)

 Parameter number_to_binary_float:
   forall (prec emax: Z) (prec_gt_0: (0 < prec)%Z) (Hmax: (prec < emax)%Z),
   Number.number -> option (binary_float prec emax).

 Parameter binary_float_to_number:
   forall (prec emax : Z)
       (prec_gt_0: (0 < prec)%Z) (Hmax: (prec < emax)%Z),
   binary_float prec emax -> option Number.number.
End BINARY_FLOAT_TO_NUMBER.

Module BinaryFloat_to_Number <: BINARY_FLOAT_TO_NUMBER.

(* len_uint: Number of digits in a Decimal.uint *)
Fixpoint len_uint (d: Decimal.uint) : Z :=
 match d with
 | Decimal.Nil => Z0
 | Decimal.D0 d' => Z.succ (len_uint d')
 | Decimal.D1 d' => Z.succ (len_uint d')
 | Decimal.D2 d' => Z.succ (len_uint d')
 | Decimal.D3 d' => Z.succ (len_uint d')
 | Decimal.D4 d' => Z.succ (len_uint d')
 | Decimal.D5 d' => Z.succ (len_uint d')
 | Decimal.D6 d' => Z.succ (len_uint d')
 | Decimal.D7 d' => Z.succ (len_uint d')
 | Decimal.D8 d' => Z.succ (len_uint d')
 | Decimal.D9 d' => Z.succ (len_uint d')
 end.

(* len_int:  number of digits in a Decimal.int *)
Definition len_int (d: Decimal.int) : Z :=
 match d with
 | Decimal.Pos u => len_uint u
 | Decimal.Neg u => len_uint u
 end.

(* simple_negate avoids the issue of which nan to use *)
Definition simple_negate {prec emax} (x: option (binary_float prec emax)) : option (binary_float prec emax) :=
 match x with
  | Some (B754_finite _ _ s m e H) => Some (B754_finite _ _ (negb s) m e H)
  | Some (B754_zero _ _ s) => Some (B754_zero _ _ (negb s))
  | Some (B754_infinity _ _ s) => Some (B754_infinity _ _ (negb s))
  | _ => None
  end.

Definition ensure_finite prec emax (x: binary_float prec emax) :=
 match x with
 | B754_finite _ _ _ _ _ _ => Some x
 | _ => None
 end.

Section ParseAndPrint.

Variable prec emax : Z.
Hypothesis prec_gt_0_ : Prec_gt_0 prec.
Hypothesis Hmax : (prec < emax)%Z.

(*  PARSING arbitrary-sized IEEE floats *)

Definition number_to_binary_float'
   (a: Decimal.int)  (* integer part of mantissa *)
   (b: Decimal.uint) (* fractional part of mantissa *)
   (e: Decimal.int)  (* exponent *)
         : option (binary_float prec emax) :=
  let m' := Decimal.app_int a b in
  match Z.of_int m' with
  | Zpos m0 =>
    let e' := (Z.of_int e - len_uint b)%Z in
    option_map (erase _ _)
    (ensure_finite prec emax (Bparse prec emax prec_gt_0_ Hmax 10 m0 e'))
  | Zneg m0 =>
    let e' := (Z.of_int e - len_uint b)%Z in
    option_map (erase _ _)
    (simple_negate (ensure_finite prec emax (Bparse prec emax prec_gt_0_ Hmax 10 m0 e')))
  | Z0 =>
    match m' with
    | Decimal.Pos _ => Some (B754_zero prec emax false)
    | Decimal.Neg _ => Some (B754_zero prec emax true)
    end
  end.

Definition number_to_binary_float (n: Number.number) : option (binary_float prec emax) :=
  (* input number [n] is a Decimal number (Hexadecimal not supported).
    If [n] is too large (overflow), produces None
    if [n] is tiny (underflow), produces a None
    if [n] is representable as a B754_finite, produces that floating point number.
 *)
  match n with
  | Number.Decimal (Decimal.Decimal a b) =>
    number_to_binary_float' a b (Decimal.Pos (Decimal.D0 Decimal.Nil))
  | Number.Decimal (Decimal.DecimalExp a b e) =>
    number_to_binary_float' a b e
  | _ => None
  end.

(** PRINTING arbitrary-size IEEE floats *)

Fixpoint do_rounding (n: nat) (round: bool) (d: Decimal.uint) : Decimal.uint * bool :=
  (* This function keeps only the first n digits of d,
     rounding down (if round=false)  or rounding up (if round=true).
     The result (fst part) is at most n digits long (trailing zeros are removed).
     The snd part of the result is the carry, true if a D1 digit should be
       prepended to the fst part of the result.
  *)
  match n with
  | O => (Decimal.Nil, round)
  | S n' =>
    match d with
    | Decimal.Nil => (Decimal.Nil, false)
    | Decimal.D0 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D1 d', false)
      else if Decimal.uint_beq d' Decimal.Nil then (Decimal.Nil, false)
      else (Decimal.D0 d', false)
    | Decimal.D1 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D2 d', false) else (Decimal.D1 d', false)
    | Decimal.D2 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D3 d', false) else (Decimal.D2 d', false)
    | Decimal.D3 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D4 d', false) else (Decimal.D3 d', false)
    | Decimal.D4 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D5 d', false) else (Decimal.D4 d', false)
    | Decimal.D5 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D6 d', false) else (Decimal.D5 d', false)
    | Decimal.D6 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D7 d', false) else (Decimal.D6 d', false)
    | Decimal.D7 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D8 d', false) else (Decimal.D7 d', false)
    | Decimal.D8 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.D9 d', false) else (Decimal.D8 d', false)
    | Decimal.D9 d' =>
      let (d', carry) := do_rounding n' round d' in
      if carry then (Decimal.Nil, true) else (Decimal.D9 d', false)
    end
 end.

(* format_mantissa' rounds the decimal number  DDDDDDDDD,
    to dec_precision digits,  rounding down (if round=false) or up (if round=true).
    If rounding up causes a carry to a number with more digits,
    return exponent 1, else exponent 0. *)
Definition format_mantissa' (dec_precision: nat) (round: bool) (d: Decimal.uint)
   : Decimal.uint * Z :=
  let (d', carry) := do_rounding dec_precision round d in
  if carry then (Decimal.D1 d', 1%Z) else (d', 0%Z).

Definition split_first_digit (m: Decimal.uint) : Decimal.uint * Decimal.uint :=
  match m with
  | Decimal.Nil => (Decimal.D0 Decimal.Nil, Decimal.Nil)
  | Decimal.D0 d' => (Decimal.D0 Decimal.Nil, d')
  | Decimal.D1 d' => (Decimal.D1 Decimal.Nil, d')
  | Decimal.D2 d' => (Decimal.D2 Decimal.Nil, d')
  | Decimal.D3 d' => (Decimal.D3 Decimal.Nil, d')
  | Decimal.D4 d' => (Decimal.D4 Decimal.Nil, d')
  | Decimal.D5 d' => (Decimal.D5 Decimal.Nil, d')
  | Decimal.D6 d' => (Decimal.D6 Decimal.Nil, d')
  | Decimal.D7 d' => (Decimal.D7 Decimal.Nil, d')
  | Decimal.D8 d' => (Decimal.D8 Decimal.Nil, d')
  | Decimal.D9 d' => (Decimal.D9 Decimal.Nil, d')
  end.

(* format_mantissa takes a sign (Decimal.Pos or Decimal.Neg)
   and a decimal mantissa  D[.]DDDDDDDD with implicit decimal point,
   and produces a rounded decimal number of the form +D.DDDDD or -D.DDDDD,
   with explicit decimal point, along with carry=1 if the implicit decimal point has
   shifted (because of carry out of high-order digit), otherwise carry=0.
   Or if input is d=zero, then no rounding or carry, just output 0.0 *)
Definition format_mantissa (dec_precision: nat)
                (round: bool)
                (sign: Decimal.uint -> Decimal.int)
                (d: Decimal.uint) : Decimal.decimal * Z :=
  if Decimal.uint_beq d Decimal.Nil then
   (Decimal.Decimal (sign (Decimal.D0 Decimal.Nil)) (Decimal.D0 Decimal.Nil), 0%Z)
  else
    let (d',carry) := format_mantissa' dec_precision round d in
    let (h,t) := split_first_digit d' in
    (Decimal.Decimal (sign h) t, carry).

(* format_mantissa_int takes a decimal mantissa  +D[.]DDDDDDDD or -D[.]DDDDDDDD
   with implicit decimal point,
   and produces a rounded decimal number of the form +D.DDDDD or -D.DDDDD,
   with explicit decimal point, along with carry=1 if the implicit decimal point has
   shifted (because of carry out of high-order digit), otherwise carry=0.
   Or if input is d=zero, then no rounding or carry, just output 0.0 *)
Definition format_mantissa_int (dec_precision: nat) (round: bool) (d: Decimal.int)
    : Decimal.decimal * Z :=
  match d with
  | Decimal.Pos d' => format_mantissa dec_precision round Decimal.Pos d'
  | Decimal.Neg d' =>format_mantissa dec_precision round Decimal.Neg d'
  end.

(* Choose a beautiful way to express the decimal number h.frac x 10^e,
   where h is a single digit.  *)
Definition perhaps_exponent (h: Decimal.int) (frac: Decimal.uint) (e: Z)
                   : Decimal.decimal :=
  match e with
  | 0%Z => Decimal.Decimal h frac
  | 1%Z => 
    let (d,r) := split_first_digit frac in
    Decimal.Decimal (Decimal.app_int h d) r
  | 2%Z =>
    let (d1,r1) := split_first_digit frac in
    let (d2,r2) := split_first_digit r1 in
    Decimal.Decimal (Decimal.app_int h (Decimal.app d1 d2)) r2
  | (-1)%Z =>
    match Decimal.app_int h frac with
    | Decimal.Pos u => Decimal.Decimal (Decimal.Pos (Decimal.D0 Decimal.Nil)) u
    | Decimal.Neg u => Decimal.Decimal (Decimal.Neg (Decimal.D0 Decimal.Nil)) u
    end
  | _ => Decimal.DecimalExp h frac (Z.to_int e)
  end.

(* format_float_num' takes a number
    (+/-)D.DDDDDDDDDDDDDD x 10^e,
   rounds it do dec_precision digits (rounding down if round=false, otherwise up),
   and produces a Number.Decimal representation.  It then validates the
   output by converting back to float and comparing with [goal].
   If success, produces Some, otherwise None. *)
Definition format_float_num'
    (goal: binary_float prec emax) (dec_precision: nat)
    (round: bool)  (d: Decimal.int) (e': Z) : option Number.number :=
  let (m, e'') := format_mantissa_int dec_precision round d in
  let e := (e'+e'')%Z in
  if Z.eqb e 0%Z
  then Some (Number.Decimal m)
  else
    match m with
    | Decimal.Decimal h t =>
      let n := Number.Decimal (perhaps_exponent h t e) in
      match number_to_binary_float n with
      | Some y =>
        match Bcompare prec emax goal y with
        | Some Eq => Some n
        | _ => None
        end
      | None => None
      end
    | _ => None
    end.


(* Measures approximately how many characters in the printed representation of n *)
Definition ugliness_of_number (n: Number.number) : Z :=
  match n with
  | Number.Decimal (Decimal.Decimal h Decimal.Nil) => len_int h
  | Number.Decimal (Decimal.Decimal h t) => len_int h + len_uint t + 1
  | Number.Decimal (Decimal.DecimalExp h Decimal.Nil (Decimal.Pos e)) =>
    len_int h + 1 + len_uint e
  | Number.Decimal (Decimal.DecimalExp h Decimal.Nil (Decimal.Neg e)) =>
    len_int h + 2 + len_uint e
  | Number.Decimal (Decimal.DecimalExp h t (Decimal.Pos e)) =>
    len_int h + len_uint t + 2 + len_uint e
  | Number.Decimal (Decimal.DecimalExp h t (Decimal.Neg e)) =>
    len_int h + len_uint t + 3 + len_uint e
  | _ => 1
  end.

Definition choose_least_ugly (a b: option Number.number) :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some n1, Some n2 =>
    if (ugliness_of_number n1 <=? ugliness_of_number n2)%Z
    then a else b
  end.

(* format_float_num takes a decimal number DDDDDDD and exponent e,
   where DDDDDDD is considered an integer (decimal point at right),
   and produces (if possible) its Number.number representation *)
Definition format_float_num
    (goal: binary_float prec emax)
    (d: Decimal.int) (e: Z) : option Number.number :=
  let dec_precision := Z.to_nat (1 + prec * 100 / 332) in
  let e' := (e + (len_int d - 1))%Z in
  let f := format_float_num' goal  in
  List.fold_left choose_least_ugly
    (f dec_precision false d e'
    :: f dec_precision true d e'
    :: f (dec_precision-1)%nat true d e'
    :: nil)
    None.

(* binary_float_to_number_nonneg takes a nonnegative floating point number x,
   and converts it (if possible) to its Number.number representation *)
Definition binary_float_to_number_nonneg
       (* x must be nonnegative! *)
       (x: binary_float prec emax) : option Number.number :=
  let '(y,e) := Bfrexp _ _ prec_gt_0_ x in
  let z := Bldexp _ _ prec_gt_0_ Hmax mode_NE y prec in
  match ZofB prec emax z with
  | None => None
  | Some i =>
    if Z.ltb prec e then
      let d := Z.to_int (i * Z.pow 2 (e-prec)) in
      format_float_num x d Z0
    else
      let d := Z.to_int (i * Z.pow 5 (prec-e)) in
      format_float_num x d (e-prec)
  end.

(*  binary_float_to_number_nonneg takes a floating point number x,
   and converts it (if possible) to its Number.number representation *)
Definition binary_float_to_number
       (x: binary_float prec emax) : option Number.number :=
  match x with
  | B754_zero _ _ false => Some (Number.Decimal (Decimal.Decimal (Decimal.Pos (Decimal.D0 Decimal.Nil)) Decimal.Nil))
  | B754_zero _ _ true => Some (Number.Decimal (Decimal.Decimal (Decimal.Neg (Decimal.D0 Decimal.Nil)) Decimal.Nil))
  | B754_nan _ _ _ _ _ => None
  | B754_infinity _ _ _ => None
  | B754_finite _ _ false _ _ _ =>  binary_float_to_number_nonneg x
  | B754_finite _ _ true m e H =>
    match binary_float_to_number_nonneg (B754_finite prec emax false m e H) with
    | Some (Number.Decimal (Decimal.Decimal (Decimal.Pos d) m)) =>
      Some (Number.Decimal (Decimal.Decimal (Decimal.Neg d) m))
    | Some (Number.Decimal (Decimal.DecimalExp (Decimal.Pos d) m e)) =>
      Some (Number.Decimal (Decimal.DecimalExp (Decimal.Neg d) m e))
    | _ => None
    end
  end.

End ParseAndPrint.

End BinaryFloat_to_Number.

Import BinaryFloat_to_Number.

Module Float32_Notation.
(* Now we instantiate this for IEEE single-precision (32-bit) floating
   point.  One could similarly instantiate it for any other precision
  (64-bit, 80-bit, 128-bit, etc.)
*)
Definition number_to_float32:  Number.number -> option (binary_float 24 128)  :=
 number_to_binary_float 24 128 ltac:(reflexivity)  ltac:(reflexivity).

Definition float32_to_number : binary_float 24 128 -> option Number.number :=
  binary_float_to_number 24 128 ltac:(reflexivity) ltac:(reflexivity).

Declare Scope float32_scope.

Notation float32xx := (binary_float 24 128) (only parsing).

(* The following Number Notation command should work, but instead
  fails with the message,
  "float32xx is bound to a notation that does not denote a reference."
  Coq issue #14806 explains what the bug is.
 *)
Fail Number Notation float32xx number_to_float32  float32_to_number
    :float32_scope.   (* It is a bug that this fails *)

(* Coq issue report #14806 proposes a workaround,
  which is to replace the constants 24 and 128 by definitions,
  as follows: *)

Definition p24 := 24%Z.
Definition p128 := 128%Z.
Notation float32x := (binary_float p24 p128) (only parsing).

Number Notation float32x number_to_float32  float32_to_number
    :float32_scope.

(* Although this workaround superficially appears to work,
   it doesn't really, as explained below. *)

Definition retype_float prec emax (x: binary_float prec emax) : binary_float prec emax :=
  match x with
  | B754_zero _ _ s => B754_zero prec emax s
  | B754_infinity _ _ s => B754_infinity prec emax s
  | B754_nan _ _ s pl e => B754_nan prec emax s pl e
  | B754_finite _ _ s m e e0 => B754_finite prec emax s m e e0
  end.

Definition rtf := retype_float p24 p128.

Local Open Scope float32_scope.

Check 0.0.  (* This correctly parses 0.0, but fails to use
 the notation to print it.  That's because it parses into
  (B754_zero 24 128 false)  instead of (B754_zero p24 p128 false).
  The value with 24 and 128 is not recognized as a float32x
  by the Number Notation printer, so it prints without benefit
  of notation.

  One might consider it a bug that the notation parser is
  explicitly for the type (binary_float p24 p128) but it is
  parsed into type (binary_float 24 128), but I don't really see that
  as the bug.  It seems that the notation parser is unfolding
  p24 and p128, but I think that's OK; and in any case, fixing
  bug #14806 would render that issue irrelevant. *)
Compute (rtf 0.0).  (* The rtf function converts the value
    (B754_zero 24 128 false)  into (B754_zero p24 p128 false),
    and then the notation printer recognizes it, and works
    correctly.  So you might think, "the workaround really worked."
   But not really:  most values that users will produce will
   be reduced to contain 24 and 128 instead of p24 and p128,
   and the use of the rtf function here is quite artificial. *)
Check -0.00001.
Compute  @Datatypes.id float32x (-0.00001).  (* This line
   illustrates that the workaround is even more fragile than
   one might have thought!   Here, the value uses p24 and p128
   as arguments to the B754_finite constructor, and has type
   binary_float p24 p128;  so you might have expected the
   notation printer to print it as -1e-5, but it does not recognize it. *)
Compute  rtf (-0.00001).   (* same comment applies as in
   the line above. *)
Eval hnf in rtf (-0.00001).  (* Surprise:  In this case,
   the pretty printer recognizes that it should use the
   Number Notation printer.   Very brittle behavior. *)

(* The remainder of these examples are just tests of the conversion
   algorithm, and don't illustrate anything new about the Coq issues.
*)
Check 0.
Compute (rtf 0).
Check 1.5.
Eval hnf in rtf 1.5.
Check 15.
Eval hnf in rtf 15.
Check 150.
Eval hnf in rtf 150.
Check 1500.
Eval hnf in rtf 1500.
Check 0.15.
Eval hnf in rtf 0.15.
Check 0.015.
Eval hnf in rtf 0.015.
Check 0.0000000001.
Eval hnf in rtf 0.0000000001.
Fail Check 1e-100. (* It is correct that this fails *)
Fail Check 1e100. (* It is correct that this fails *)
Check 1e20.
Eval hnf in rtf 1e20.
Check 1e-20.
Eval hnf in rtf 1e-20.

End Float32_Notation.


