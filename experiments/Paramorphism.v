Require Import Coq.Lists.List.
Import ListNotations.

Definition Paramorphism {A B : Type} (f: A -> list A -> B -> B) (z:B)
  : list A -> B
  :=
    fix h l :=
      match l with
      | [] => z
      | x::xs => f x xs (h xs)
      end.
