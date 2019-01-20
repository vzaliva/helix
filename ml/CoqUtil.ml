open Camlcoq
open Core

let positivie_of_int63 i63 =
  Int63.to_int64 i63 |> P.of_int64

let binary_float_of_camlfloat f =
  let open Binary in
  let s = Float.is_negative f in
  if Float.equal f Float.zero then B754_zero s
  else if Float.is_nan f then B754_nan (s, positivie_of_int63 (Float.ieee_mantissa f))
  else if Float.is_inf f then B754_infinity s
  else B754_finite (s,
                    positivie_of_int63 (Float.ieee_mantissa f),
                    Z.of_sint (Float.ieee_exponent f))
