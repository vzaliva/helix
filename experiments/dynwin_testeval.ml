(* FILE: ml/testeval.ml *)

(* [...] *)

(* polynomial coefficients *)
let a = [0.21; 1.2; 0.5]
(* robot speed *)
let v_r = [1.0]
(* robot position *)
let p_r = [0.0; 0.0]
(* obstact position *)
let p_o = [1.0; 1.0]
(* the initial value of the output block;
   should not affect anything and should be overwritten *)
let random = [314.15]

let dynwin_test_inp = 
  random
  @ v_r @ p_r @ p_o
  @ a

let dynwin_test t =
  process_test t (List.map dynwin_test_inp ~f:coqfloat_of_camlfloat)

let _ =
  Arg.parse args (fun _ -> ())  "USAGE: ./testcomp [-v] [-p] [t <name>]\n";
  if !printtests
  then
    begin
      ignore (List.map all_tests
                ~f:(fun t -> Printf.printf "%s\n" (camlstring_of_coqstring (name t))));
      exit 0
    end
  else
    let open Core.String in
    let t = if !single = "" then all_tests
            else List.filter all_tests ~f:(fun x -> camlstring_of_coqstring (name x) = !single) in
    exit (if List.fold ((* List.map t ~f:random_test @ *) List.map t ~f:dynwin_test) ~init:true ~f:(&&)
          then 0 else 1)
