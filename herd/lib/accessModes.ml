(* Java Access Modes *)

type t = Plain
       | Opaque
       | Acquire
       | Release
       | Volatile

let compare = compare

(* pretty print *)
let pp_access_modes = function
  | Plain    -> "Plain"
  | Opaque   -> "Opaque"
  | Acquire  -> "Acquire"
  | Release  -> "Release"
  | Volatile -> "Volatile"
