open Camlcoq
open Core

let rec positive_of_int x =
  let open BinNums in
  if x = 1 then Coq_xH else
    let xs = positive_of_int (x asr 1) in
    if x land 1 = 1 then Coq_xI xs else Coq_xO xs

let positivie_of_int63 i63 =
  match Int63.to_int i63 with
  | None -> failwith "It looks like we are on unsupported 32 bit platform!"
  | Some x -> positive_of_int x

let binary_float_of_float f =
  let open Binary in
  let s = Float.is_negative f in
  if Float.equal f Float.zero then B754_zero s
  else if Float.is_nan f then B754_nan (s, positivie_of_int63 (Float.ieee_mantissa f))
  else if Float.is_inf f then B754_infinity s
  else B754_finite (s,
                    positivie_of_int63 (Float.ieee_mantissa f),
                    Z.of_sint (Float.ieee_exponent f))
