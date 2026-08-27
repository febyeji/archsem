(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

(** Convert Isla IR to Testrepr.t.

    Pipeline: IR -> Assembler.assembly_input -> Assembler.assemble -> Testrepr.t.
    The converter fixes the VA layout for code/data symbols before calling the
    assembler. The assembler only emits code bytes and applies relocations for
    those preassigned addresses. The converter then evaluates terms and builds
    registers, memory, termination, and outcomes. *)

open Litmus
module RegValGen = Archsem.RegValGen
module Assertion = Litmus.Assertion

(* Fix lem/linksem dirty stuff *)
module Either = Stdlib.Either

(** {1 Setup} *)

(** {2 Config helpers} *)

let pc_reg arch =
  match arch with
  | Litmus.Arch_id.Arm -> Archsem.Arm.Reg.to_string Archsem.Arm.Reg.pc
  | Litmus.Arch_id.X86 -> Archsem.X86.Reg.to_string Archsem.X86.Reg.pc

let register_defaults =
  Config.make_getter ~default:[]
    (Toml.get_table_values Litmus.Parser.toml_to_gen)
    ["registers"; "defaults"]

let instruction_step =
  Config.make_getter Toml.get_positive ["assembler"; "instruction_step"]

let default_memory_size =
  Config.make_getter Toml.get_positive ["isla"; "default_memory_size"]

(** {2 Evaluation errors} *)

type eval_context =
  | Location_init of string
  | Register_init of int * string
  | Breakpoints of int
  | Final_assertion
  | Page_table_setup

exception Eval_error of string list * string

let eval_context_path = function
  | Location_init sym -> ["locations"; sym]
  | Register_init (tid, reg) -> ["thread"; string_of_int tid; "init"; reg]
  | Breakpoints tid -> ["thread"; string_of_int tid; "breakpoints"]
  | Final_assertion -> ["final"; "assertion"]
  | Page_table_setup -> ["page_table_setup"]

(** {1 Conversion helpers} *)

(** {2 Term evaluation} *)

let eval_error context fmt =
  Printf.ksprintf
    (fun msg -> raise (Eval_error (eval_context_path context, msg)))
    fmt

let eval_term ?page_table_entries ?page_table_pages ~context ~lookup_addr term =
  try
    let value =
      Term.eval ?page_table_entries ?page_table_pages ~lookup_addr term
    in
    match context with
    (* Final constants stay raw Z.t; registers read via bv_unsigned. *)
    | Final_assertion when Z.sign value < 0 ->
        eval_error context "final assertion values must be non-negative: %s"
          (Z.format "%#x" value)
    | Breakpoints _ when Z.sign value < 0 ->
        eval_error context "Breakpoint values must be non-negative: %s"
          (Z.format "%#x" value)
    | _ -> value
  with Failure msg -> eval_error context "%s" msg

let normalize_register_gen ~arch ~context reg_name gen =
  try
    match arch with
    | Litmus.Arch_id.Arm ->
        Archsem.Arm.RegVal.(to_gen (of_string_gen reg_name gen))
    | Litmus.Arch_id.X86 ->
        Archsem.X86.RegVal.(to_gen (of_string_gen reg_name gen))
  with Failure msg -> eval_error context "%s" msg

(** {2 Address layout} *)

(* Explicit section addresses are already consumed before allocation starts.
   This assumes each assembled named section fits in one allocator page. *)
let reserved_section_addrs sections =
  List.filter_map (fun (sec : Ir.section) -> sec.address) sections

let thread_section_name tid = Printf.sprintf "__thread%d" tid

let block_base size addr = addr - (addr mod size)

let unique_blocks addrs =
  List.map (block_base Allocator.big_size) addrs |> List.sort_uniq Int.compare

let regions_of_blocks blocks =
  List.map (fun base -> Allocator.{base; size = Allocator.big_size}) blocks

let symbolic_names ir =
  let add names name = if List.mem name names then names else names @ [name] in
  let rec collect names = function
    | [] -> names
    | Page_table_ast.Virtual stmt_names :: stmts ->
        collect (List.fold_left add names stmt_names) stmts
    | Page_table_ast.TableBlock {body; _} :: stmts ->
        collect (collect names body) stmts
    | _ :: stmts -> collect names stmts
  in
  collect ir.Ir.symbolic ir.Ir.page_table_setup

let checked_virtual_alignment alignment =
  let alignment =
    try Z.to_int alignment
    with Z.Overflow ->
      eval_error Page_table_setup "page_table: virtual alignment is out of range"
  in
  if alignment <= 0 || alignment mod Allocator.page_size <> 0 then
    eval_error Page_table_setup
      "page_table: virtual alignment must be a positive multiple of page size: %d"
      alignment;
  alignment

let checked_mapping_alignment level =
  try Page_table_desc.level_size level
  with Invalid_argument _ ->
    eval_error Page_table_setup "page_table: invalid mapping level: %d" level

let symbolic_va_alignments ir =
  let virtual_names = symbolic_names ir in
  let rec collect = function
    | [] -> []
    | Page_table_ast.AlignedVirtual {alignment; names} :: stmts ->
        let alignment = checked_virtual_alignment alignment in
        List.iter
          (fun name ->
             if not (List.mem name virtual_names) then
               eval_error Page_table_setup "page_table: undeclared VA: %s" name
           )
          names;
        List.map (fun name -> (name, alignment)) names @ collect stmts
    | Page_table_ast.Mapping {va_name; level = Some level; _} :: stmts
     |Page_table_ast.MaybeMapping {va_name; level = Some level; _} :: stmts ->
        (va_name, checked_mapping_alignment level) :: collect stmts
    | Page_table_ast.TableBlock {body; _} :: stmts -> collect body @ collect stmts
    | _ :: stmts -> collect stmts
  in
  let alignment_requests = collect ir.Ir.page_table_setup in
  let alignment_for name =
    List.fold_left
      (fun best (aligned_name, alignment) ->
         if aligned_name = name then max best alignment else best
       )
      Allocator.page_size alignment_requests
  in
  List.map (fun name -> (name, alignment_for name)) virtual_names

type allocation_layout =
  { code_allocator : Allocator.t;
    code_blocks : int list;
    alloc_data : alignment:int -> int;
    table_allocator : Allocator.t option;
    table_blocks : int list
  }

let make_linear_allocation sections =
  let allocator = Allocator.make ~reserved:(reserved_section_addrs sections) () in
  { code_allocator = allocator;
    code_blocks = [];
    alloc_data =
      (fun ~alignment ->
        Allocator.alloc_aligned allocator ~size:Allocator.page_size ~alignment
      );
    table_allocator = None;
    table_blocks = []
  }

let mapping_table_addr = function
  | Page_table_ast.Mapping {target = Page_table_ast.Table addr; _}
   |Page_table_ast.MaybeMapping {target = Page_table_ast.Table addr; _} ->
      Some addr
  | _ -> None

let fixed_code_pages stmts =
  let to_int addr =
    try Z.to_int addr
    with Z.Overflow ->
      eval_error Page_table_setup "page_table: code address is out of range"
  in
  let rec collect = function
    | [] -> []
    | Page_table_ast.IdentityMapping {addr; attr = Page_table_ast.Code} :: stmts
      ->
        to_int addr :: collect stmts
    | Page_table_ast.TableBlock {body; _} :: stmts -> collect body @ collect stmts
    | _ :: stmts -> collect stmts
  in
  collect stmts |> List.sort_uniq Int.compare

let fixed_table_pages stmts =
  let to_int addr =
    try Z.to_int addr
    with Z.Overflow ->
      eval_error Page_table_setup "page_table: table address is out of range"
  in
  let rec collect = function
    | [] -> []
    | Page_table_ast.TableBlock {base; body; _} :: stmts ->
        to_int base :: (collect body @ collect stmts)
    | Page_table_ast.IdentityMapping {addr; attr = Page_table_ast.Default}
      :: stmts ->
        to_int addr :: collect stmts
    | stmt :: stmts ->
        Option.map to_int (mapping_table_addr stmt)
        |> Option.to_list
        |> fun pages -> pages @ collect stmts
  in
  collect stmts |> List.sort_uniq Int.compare

let required_code_pages ir =
  List.length ir.Ir.threads
  + List.length (List.filter (fun sec -> sec.Ir.address = None) ir.Ir.sections)

let make_regional_allocation ir =
  let occupied_code_pages = reserved_section_addrs ir.Ir.sections in
  let code_arena_addrs =
    occupied_code_pages @ fixed_code_pages ir.Ir.page_table_setup
    |> List.sort_uniq Int.compare
  in
  let fixed_pgt_pages = fixed_table_pages ir.Ir.page_table_setup in
  let code_blocks = unique_blocks code_arena_addrs in
  let table_blocks = unique_blocks fixed_pgt_pages in
  let overlap =
    List.filter (fun block -> List.mem block table_blocks) code_blocks
  in
  if overlap <> [] then
    eval_error Page_table_setup
      "page_table: code and page-table storage share 2MB block 0x%x"
      (List.hd overlap);
  let fixed_blocks = code_blocks @ table_blocks in
  let l1_size = 1 lsl 30 in
  let l1_base =
    match fixed_blocks with [] -> 0 | block :: _ -> block_base l1_size block
  in
  List.iter
    (fun block ->
       if block_base l1_size block <> l1_base then
         eval_error Page_table_setup
           "page_table: fixed storage addresses span multiple 1GB regions"
     )
    fixed_blocks;
  let arena_allocator =
    Allocator.make_in_regions ~reserved:fixed_blocks
      [Allocator.{base = l1_base; size = l1_size}]
  in
  let reserved_code_pages = 0 :: occupied_code_pages in
  let reserved_code_page_count =
    List.filter
      (fun addr -> List.mem (block_base Allocator.big_size addr) code_blocks)
      reserved_code_pages
    |> List.map (block_base Allocator.page_size)
    |> List.sort_uniq Int.compare |> List.length
  in
  let rec add_code_blocks blocks =
    let capacity =
      (List.length blocks * (Allocator.big_size / Allocator.page_size))
      - reserved_code_page_count
    in
    if capacity >= required_code_pages ir && blocks <> [] then blocks
    else add_code_blocks (blocks @ [Allocator.alloc_big arena_allocator])
  in
  let code_blocks = add_code_blocks code_blocks in
  let code_allocator =
    Allocator.make_in_regions ~reserved:reserved_code_pages
      (regions_of_blocks code_blocks)
  in
  let regular_data_block = Allocator.alloc_big arena_allocator in
  let data_allocator =
    Allocator.make_in_regions ~reserved:[0]
      (regions_of_blocks [regular_data_block])
  in
  let alloc_data ~alignment =
    if alignment >= Allocator.big_size then
      Allocator.alloc_aligned arena_allocator ~size:Allocator.big_size ~alignment
    else
      Allocator.alloc_aligned data_allocator ~size:Allocator.page_size ~alignment
  in
  let table_blocks =
    match table_blocks with
    | [] -> [Allocator.alloc_big arena_allocator]
    | blocks -> blocks
  in
  let table_allocator =
    Allocator.make_in_regions ~reserved:fixed_pgt_pages
      (regions_of_blocks table_blocks)
  in
  { code_allocator;
    code_blocks;
    alloc_data;
    table_allocator = Some table_allocator;
    table_blocks
  }

(* Build assembly input after assigning concrete addresses to every section and
   symbolic location. *)
let to_assembly_input allocation (ir : Ir.t) : Assembler.assembly_input =
  let code_sections =
    List.mapi
      (fun i (thread : Ir.thread) ->
         { Assembler.name = thread_section_name i;
           code = thread.code;
           addr = Allocator.alloc_page allocation.code_allocator
         }
       )
      ir.threads
  in
  let named_sections =
    List.map
      (fun (sec : Ir.section) ->
         let addr =
           match sec.address with
           | Some addr -> addr
           | None -> Allocator.alloc_page allocation.code_allocator
         in
         {Assembler.name = sec.sec_name; code = sec.code; addr}
       )
      ir.sections
  in
  let symbols =
    List.map
      (fun (name, alignment) ->
         let addr = allocation.alloc_data ~alignment in
         {Assembler.name; addr}
       )
      (symbolic_va_alignments ir)
  in
  {Assembler.sections = code_sections @ named_sections; symbols}

(** {2 Thread register construction} *)

let find_section name (asm_result : Assembler.assembly_result) =
  List.find
    (fun (s : Assembler.linked_section) -> s.name = name)
    asm_result.sections

(* Build per-thread initial register maps: PC + user init + config defaults. *)
let build_registers
      ~arch
      ?page_table_entries
      ?page_table_pages
      ?page_table_root
      ~lookup_addr
      ~pc
      (start_pc : int)
      (thread : Ir.thread)
  =
  let pc_entry = (pc, RegValGen.Number (Z.of_int start_pc)) in
  let used_regs =
    List.map
      (fun (reg, value) ->
         let context = Register_init (thread.tid, reg) in
         let gen =
           RegValGen.Number
             (eval_term ?page_table_entries ?page_table_pages ~context
                ~lookup_addr value
             )
         in
         (reg, normalize_register_gen ~arch ~context reg gen)
       )
      thread.regs
  in
  let base_regs = pc_entry :: used_regs in
  let has regs name = List.exists (fun (reg, _) -> reg = name) regs in
  let base_regs =
    match page_table_root with
    | Some root when not (has base_regs "TTBR0_EL1") ->
        base_regs @ [("TTBR0_EL1", RegValGen.Number (Z.of_int root))]
    | _ -> base_regs
  in
  let default_regs =
    List.filter_map
      (fun (reg, value) -> if has base_regs reg then None else Some (reg, value))
      (register_defaults ())
  in
  base_regs @ default_regs

let build_threads
      ~arch
      ?page_table_entries
      ?page_table_pages
      ?page_table_root
      ~lookup_addr
      asm_result
      (threads : Ir.thread list) : Testrepr.thread list
  =
  let pc = pc_reg arch in
  List.mapi
    (fun tid (thread : Ir.thread) ->
       let sec = find_section (thread_section_name tid) asm_result in
       let regs =
         build_registers ~arch ?page_table_entries ?page_table_pages
           ?page_table_root ~lookup_addr ~pc sec.addr thread
       in
       let breakpoints =
         let context = Breakpoints tid in
         Z.of_int (sec.addr + Bytes.length sec.data)
         :: List.map
              (eval_term ?page_table_entries ?page_table_pages ~context
                 ~lookup_addr
              )
              thread.breakpoints
       in
       {Testrepr.regs; breakpoints}
     )
    threads

(** {2 Page table setup construction} *)

(* Build the page-table layout from concrete section/symbol VAs. *)
let build_page_table_setup ir allocation asm_result =
  match ir.Ir.page_table_setup with
  | [] -> None
  | page_table_setup -> (
      if ir.Ir.locations <> [] then
        eval_error Page_table_setup
          "page_table: [locations] is not supported with page_table_setup";
      let symbolic_vas = asm_result.Assembler.symbols in
      try
        Some
          ( match allocation.table_allocator with
          | None -> assert false
          | Some table_allocator ->
              Page_table_builder.build ~arch:ir.arch
                ~alloc_data:allocation.alloc_data ~table_allocator
                ~code_blocks:allocation.code_blocks
                ~table_blocks:allocation.table_blocks ~symbolic_vas
                page_table_setup
          )
      with Page_table_builder.Error msg -> eval_error Page_table_setup "%s" msg
    )

(* Terms may refer to VA-side assembly symbols and PA-side symbols created by
   page_table_setup. *)
let build_lookup_addr asm_result page_table =
  let page_table_symbols =
    match page_table with
    | None -> []
    | Some layout ->
        let default_root =
          Option.map
            (fun root -> ("page_table_base", root))
            layout.Page_table_builder.default_root
          |> Option.to_list
        in
        default_root @ layout.Page_table_builder.table_symbols_pa
        @ layout.Page_table_builder.data_symbols_pa
  in
  let symbols_addr = asm_result.Assembler.symbols @ page_table_symbols in
  fun name ->
    match List.assoc_opt name symbols_addr with
    | Some addr -> addr
    | None -> Printf.ksprintf failwith "Symbol %s not found" name

(** {2 Memory construction} *)

let symbol_size ~default symbol_sizes sym =
  List.assoc_opt sym symbol_sizes |> Option.value ~default

(* Encode integer initialisers as fixed-size little-endian byte strings. *)
let init_bytes_of_value mem_size label value =
  let bit_width = mem_size * 8 in
  if Z.numbits value > bit_width then
    Error.fatal "Number doesn't fit in symbol %s" label;
  let value = Z.extract value 0 bit_width in
  let data = Bytes.make mem_size '\x00' in
  let bits = Z.to_bits value in
  Bytes.blit_string bits 0 data 0 (min mem_size (String.length bits));
  data

let build_code ~instruction_step (asm_result : Assembler.assembly_result) =
  List.map
    (fun (sec : Assembler.linked_section) ->
       { Testrepr.addr = sec.addr;
         step = instruction_step;
         data = sec.data;
         sym = Some sec.name;
         kind = Testrepr.Code
       }
     )
    asm_result.Assembler.sections

let data_memory_block ~step ?(kind = Testrepr.Data) ?symbol addr value :
  Testrepr.memory_block
  =
  let label = Option.value symbol ~default:(Printf.sprintf "0x%x" addr) in
  { Testrepr.addr;
    step;
    data = init_bytes_of_value step label value;
    sym = symbol;
    kind
  }

(* Build backing data blocks for declared symbolic locations. *)
let build_locations_memory
      ~default_mem_size
      ~symbol_sizes
      ~symbols
      ~lookup_addr
      ~locations
  =
  List.map
    (fun (sym : Assembler.data_symbol) ->
       let mem_size =
         symbol_size ~default:default_mem_size symbol_sizes sym.name
       in
       let value =
         List.assoc_opt sym.name locations
         |> Option.map (eval_term ~context:(Location_init sym.name) ~lookup_addr)
         |> Option.value ~default:Z.zero
       in
       data_memory_block ~step:mem_size ~symbol:sym.name sym.addr value
     )
    symbols

let build_page_table_memory ~default_mem_size ~symbol_sizes page_table =
  let table_memory =
    List.map
      (fun (addr, value) ->
         data_memory_block ~step:Page_table_desc.entry_size
           ~kind:Testrepr.PageTable addr (Z.of_int64 value)
       )
      page_table.Page_table_builder.table_entries
  in
  let phys_memory =
    List.map
      (fun (sym, pa) ->
         let mem_size = symbol_size ~default:default_mem_size symbol_sizes sym in
         let value =
           List.assoc_opt pa page_table.Page_table_builder.data_inits
           |> Option.value ~default:Z.zero
         in
         data_memory_block ~step:mem_size ~symbol:sym pa value
       )
      page_table.Page_table_builder.data_symbols_pa
  in
  table_memory @ phys_memory

(* Build the final Testrepr memory from assembled code plus whichever data
   representation the test uses. *)
let build_memory
      ~default_mem_size
      ~symbol_sizes
      ~data_symbols
      ~lookup_addr
      ~locations
      asm_result
      page_table
  =
  let code_memory =
    build_code ~instruction_step:(instruction_step ()) asm_result
  in
  let data_memory =
    match page_table with
    | None ->
        build_locations_memory ~default_mem_size ~symbol_sizes
          ~symbols:data_symbols ~lookup_addr ~locations
    | Some page_table ->
        build_page_table_memory ~default_mem_size ~symbol_sizes page_table
  in
  code_memory @ data_memory

(** {1 Public API} *)

let to_testrepr ~filename (ir : Ir.t) : Testrepr.t =
  let default_mem_size = default_memory_size () in
  let allocation =
    match ir.page_table_setup with
    | [] -> make_linear_allocation ir.sections
    | _ -> make_regional_allocation ir
  in
  let asm_input = to_assembly_input allocation ir in
  let asm_result = Assembler.assemble ~filename asm_input in
  let page_table = build_page_table_setup ir allocation asm_result in
  let page_table_entries =
    Option.map (fun layout -> layout.Page_table_builder.table_entries) page_table
  in
  let page_table_pages =
    Option.map (fun layout -> layout.Page_table_builder.table_pages) page_table
  in
  let lookup_addr = build_lookup_addr asm_result page_table in
  let page_table_root =
    Option.bind page_table (fun layout -> layout.Page_table_builder.default_root)
  in
  let threads =
    build_threads ~arch:ir.arch ?page_table_entries ?page_table_pages
      ?page_table_root ~lookup_addr asm_result ir.threads
  in
  let memory =
    build_memory ~default_mem_size ~symbol_sizes:ir.sizes
      ~data_symbols:asm_input.symbols ~lookup_addr ~locations:ir.locations
      asm_result page_table
  in
  { arch = Litmus.Arch_id.to_string ir.arch;
    name = ir.name;
    threads;
    memory;
    kind = ir.kind;
    final =
      Assertion.map_cst
        (eval_term ?page_table_entries ?page_table_pages ~context:Final_assertion
           ~lookup_addr
        )
        ir.assertion
  }
