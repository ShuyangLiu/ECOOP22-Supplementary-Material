module Make (A : Arch_herd.S) : sig

  type action =
    | Access of Dir.dirn * A.location * A.V.v * MemOrderOrAnnot.t * MachSize.sz
    | Fence of MemOrderOrAnnot.t
    | RMW of A.location * A.V.v * A.V.v * MemOrderOrAnnot.t * MachSize.sz

  include Action.S with type action := action and module A = A

end = struct

  module A = A
  module V = A.V
  open Dir
  open Printf
  open MemOrderOrAnnot

  type action =
    | Access of Dir.dirn * A.location * A.V.v * MemOrderOrAnnot.t * MachSize.sz
    | Fence of MemOrderOrAnnot.t
    | RMW of A.location * A.V.v * A.V.v * MemOrderOrAnnot.t * MachSize.sz

  let mk_init_write l sz v = Access (W,l,v,AN [],sz)

  let par f x = sprintf "(%s)" (f x) (*for access modes*)

  let pp_action a =
    match a with
    | Access (d, l, v, mo, _) ->
        (sprintf "%s%s%s=%s"
                (pp_dirn d)
                (match mo with
                | AM am -> par AccessModes.pp_access_modes am
                | _ -> "")
                (A.pp_location l)
                (V.pp_v v))

    | Fence b ->
        sprintf "F%s"
          (match b with
           | AM am -> par AccessModes.pp_access_modes am
           | _ -> "")

    | RMW (l, v1, v2, am, _) ->
        (sprintf "RMW(%s)%s(%s>%s)"
                (match am with
               | AM am -> (AccessModes.pp_access_modes am)
               | _ -> "")
                (A.pp_location l)
                (V.pp_v v1)
                (V.pp_v v2))

  let is_isync _ = raise Misc.NoIsync
  let pp_isync = "???"

  let is_barrier a = match a with
  | Fence _ -> true
  | _ -> false

  let barrier_of _ = assert false
  let same_barrier_id _ _ = assert false

  let is_rmw a = match a with
  | RMW _ -> true
  | _ -> false

  let is_reg a (p:int) = match a with
  | Access (_,A.Location_reg (q,_),_,_,_) -> p = q
  | _ -> false

  let is_mem a = match a with
  | Access (_,A.Location_global _,_,_,_) -> true
  | RMW (A.Location_global _,_,_,_,_) -> true
  | _ -> false

  let is_additional_mem _ = false

  let is_additional_mem_load _ = false

  let is_atomic a = match a with
  | Access (_,A.Location_global _,_,_,_) -> true
  | RMW _ -> true
  | _ -> false

  let to_fault _ = None

  let is_reg_store a (p:int) = match a with
  | Access (W,A.Location_reg (q,_),_,_,_) -> p = q
  | _ -> false

  let is_reg_load a (p:int) = match a with
  | Access (R,A.Location_reg (q,_),_,_,_) -> p = q
  | _ -> false

  let is_reg_any a = match a with
  | Access (_,A.Location_reg _,_,_,_) -> true
  | _ -> false

  let get_mem_dir a = match a with
  | Access (d,A.Location_global _,_,_,_) -> d
  | _ -> assert false

  let get_mem_size a = match a with
  | Access (_,A.Location_global _,_,_,sz) -> sz
  | _ -> assert false

  let is_mem_store a = match a with
  | Access (W,A.Location_global _,_,_,_)
  | RMW (A.Location_global _,_,_,_,_)
    -> true
  | _ -> false

  let is_mem_load a = match a with
  | Access (R,A.Location_global _,_,_,_)
  | RMW (A.Location_global _,_,_,_,_)
    -> true
  | _ -> false

  let value_of a = match a with
  | Access (_,_,v,_,_) -> Some v
  | _ -> None

  let read_of a = match a with
  | Access (R,_ , v,_,_)
  | RMW (_,v,_,_,_)
    -> Some v
  | _ -> None

  let written_of a = match a with
  | Access (W,_ , v,_,_)
  | RMW (_,_,v,_,_)
    -> Some v
  | _ -> None

  let location_of a = match a with
  | Access (_, l, _,_,_) -> Some l
  | RMW (l,_,_,_,_) -> Some l
  | Fence _ -> None

(* Store/Load anywhere *)
  let is_store a = match a with
  | Access (W,_,_,_,_)
  | RMW _
    -> true
  | _ -> false

  let is_load a = match a with
  | Access (R,_,_,_,_)
  | RMW _ -> true
  | _ -> false

  let is_reg_any a = match a with
  | Access (_,A.Location_reg _,_,_,_) -> true
  | _ -> false

  let is_reg_store_any a = match a with
  | Access (W,A.Location_reg _,_,_,_) -> true
  | _ -> false

  let is_reg_load_any a = match a with
  | Access (R,A.Location_reg _,_,_,_) -> true
  | _ -> false

  let compatible_accesses a1 a2 =
    (is_mem a1 && is_mem a2) || (is_reg_any a1 && is_reg_any a2)

(* (No) commits *)
  let is_commit_bcc _ = false
  let is_commit_pred _ = false

  let annot_in_list str ac = match ac with
  | Access (_,_,_,AN a,_)
    -> List.exists (fun a -> Misc.string_eq str a) a
  | _ -> false


  let mo_matches target a = match a with
  | Access(_,_,_,AM mo,_)
  | RMW (_,_,_,AM mo,_)
  | Fence (AM mo) -> (mo = target)
  | _ -> false


let undetermined_vars_in_action a =
    match a with
    | Access (_,l,v,_,_)->
        let undet_loc = match A.undetermined_vars_in_loc l with
        | None -> V.ValueSet.empty
        | Some v -> V.ValueSet.singleton v in
        if V.is_var_determined v then undet_loc
        else V.ValueSet.add v undet_loc
    | RMW(l,v1,v2,_,_) ->
        let undet_loc = match A.undetermined_vars_in_loc l with
        | None -> V.ValueSet.empty
        | Some v -> V.ValueSet.singleton v in
        let undet_loc =
          (if V.is_var_determined v1 then undet_loc
          else V.ValueSet.add v1 undet_loc) in
        let undet_loc =
          (if V.is_var_determined v2 then undet_loc
          else V.ValueSet.add v2 undet_loc) in
        undet_loc
    | Fence _ -> V.ValueSet.empty

  let simplify_vars_in_action soln a =
    match a with
    | Access (d,l,v,mo,sz) ->
        let l' = A.simplify_vars_in_loc soln l in
        let v' = V.simplify_var soln v in
        Access (d,l',v',mo,sz)
    | RMW(l,v1,v2,mo,sz) ->
        let l' = A.simplify_vars_in_loc soln l in
        let v1' = V.simplify_var soln v1 in
        let v2' = V.simplify_var soln v2 in
        RMW(l',v1',v2',mo,sz)
    | Fence _ -> a


  let arch_sets = [
    "RMW", (fun e -> is_rmw e);
    "REL", mo_matches AccessModes.Release;
    "V", mo_matches AccessModes.Volatile;
    "ACQ", mo_matches AccessModes.Acquire;
    "RA", (fun e ->
        mo_matches AccessModes.Acquire e ||
        mo_matches AccessModes.Release e);
    "O", mo_matches AccessModes.Opaque
 ]

  let arch_fences = []

end
