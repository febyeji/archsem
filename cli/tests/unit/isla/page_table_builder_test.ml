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

(** Unit tests for Isla.Page_table_builder. *)

open OUnit2

let make_layout stmts =
  let data_allocator = Isla.Allocator.make ~base:0x400000 () in
  let table_allocator =
    Isla.Allocator.make_in_regions
      [Isla.Allocator.{base = 0x200000; size = Isla.Allocator.big_size}]
  in
  Isla.Page_table_builder.build ~arch:Litmus.Arch_id.Arm
    ~alloc_data:(fun ~alignment ->
      Isla.Allocator.alloc_aligned data_allocator ~size:Isla.Allocator.page_size
        ~alignment
    )
    ~table_allocator ~code_blocks:[0] ~table_blocks:[0x200000]
    ~symbolic_vas:[("x", 0x600000)]
    stmts

let test_materialize_physical_declaration _ =
  let layout = make_layout [Isla.Page_table_ast.Physical ["pa_unused"]] in
  assert_bool "physical-only symbol is allocated"
    (List.mem_assoc "pa_unused" layout.phys_symbols_pa)

let test_mapping_alignment_is_known_before_data_init _ =
  let layout =
    make_layout
      [ Isla.Page_table_ast.DataInit {pa_name = "pa_pad"; value = Z.zero};
        Isla.Page_table_ast.DataInit {pa_name = "pa_x"; value = Z.one};
        Isla.Page_table_ast.Mapping
          { va_name = "x";
            target = Isla.Page_table_ast.PaName "pa_x";
            level = Some 2;
            attrs = []
          }
      ]
  in
  let pa_x = List.assoc "pa_x" layout.phys_symbols_pa in
  assert_equal 0 (pa_x mod Isla.Allocator.big_size)

let test_code_identity_inside_reserved_block_is_already_satisfied _ =
  let layout =
    make_layout
      [ Isla.Page_table_ast.IdentityMapping
          {addr = Z.of_int 0x1000; attr = Isla.Page_table_ast.Code}
      ]
  in
  assert_equal (Some 0x1400)
    (Isla.Page_table_builder.translate_va_to_pa layout 0x1400)

let tests =
  "Isla.Page_table_builder"
  >::: [ "materialize physical declaration"
         >:: test_materialize_physical_declaration;
         "mapping alignment is known before data init"
         >:: test_mapping_alignment_is_known_before_data_init;
         "code identity inside reserved block is already satisfied"
         >:: test_code_identity_inside_reserved_block_is_already_satisfied
       ]

let () = run_test_tt_main tests
