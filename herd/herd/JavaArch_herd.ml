(** Define Java architecture *)

module Make (C:Arch_herd.Config) (V:Value.S) = struct
  include JavaBase

  let is_amo _ = false
  let pp_barrier_short = pp_barrier
  let reject_mixed = false
  let mem_access_size _ = None

  module V = V

  include ArchExtra_herd.Make(C)
      (struct
        module V = V
        let endian = endian
        type arch_reg = reg
        let pp_reg = pp_reg
        let reg_compare = reg_compare
        type arch_instruction = instruction
        let fromto_of_instr _ = None
      end)
end