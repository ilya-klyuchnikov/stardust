(* Stardust glue/header.sml *)
structure Main :>
  sig
  end
=
struct
  datatype ('left, 'right) sum =
    Inl of 'left
  | Inr of 'right

(* end of glue/header.sml *)

