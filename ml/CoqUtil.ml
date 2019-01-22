open Camlcoq
open Core

let positivie_of_int63 i63 =
  Int63.to_int64 i63 |> P.of_int64

