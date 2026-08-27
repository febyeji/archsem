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

let make_layout ?(reserved = []) stmts =
  let data_allocator = Isla.Allocator.make ~base:0x400000 () in
  let table_allocator =
    Isla.Allocator.make_in_regions ~reserved
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
    (List.mem_assoc "pa_unused" layout.data_symbols_pa)

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
  let pa_x = List.assoc "pa_x" layout.data_symbols_pa in
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

let table_block stage name base body =
  Isla.Page_table_ast.TableBlock {stage; name; base = Z.of_int base; body}

let test_named_and_nested_roots_keep_actual_addresses _ =
  let layout =
    make_layout ~reserved:[0x280000; 0x281000]
      [ table_block Isla.Page_table_ast.S2 "outer" 0x280000
          [table_block Isla.Page_table_ast.S1 "inner" 0x281000 []]
      ]
  in
  assert_equal 0x280000 (List.assoc "outer" layout.table_symbols_pa);
  assert_equal 0x281000 (List.assoc "inner" layout.table_symbols_pa)

let test_explicit_table_target_keeps_actual_address _ =
  let layout =
    make_layout ~reserved:[0x283000]
      [ Isla.Page_table_ast.Mapping
          { va_name = "x";
            target = Isla.Page_table_ast.Table (Z.of_int 0x283000);
            level = Some 2;
            attrs = []
          }
      ]
  in
  assert_bool "explicit target is a known table page"
    (List.mem 0x283000 layout.table_pages);
  assert_bool "descriptor contains the actual target PA"
    (List.exists (fun (_, desc) -> desc = 0x283003L) layout.table_entries)

let test_duplicate_named_root_is_rejected _ =
  assert_raises
    (Isla.Page_table_builder.Error "page_table: duplicate table root: dup")
    (fun () ->
       ignore
         (make_layout ~reserved:[0x280000; 0x281000]
            [ table_block Isla.Page_table_ast.S1 "dup" 0x280000 [];
              table_block Isla.Page_table_ast.S2 "dup" 0x281000 []
            ]
         )
  )

let test_default_tables_false_uses_only_named_roots _ =
  let layout =
    make_layout ~reserved:[0x280000]
      [ Isla.Page_table_ast.OptionDefaultTables false;
        table_block Isla.Page_table_ast.S1 "only_root" 0x280000 []
      ]
  in
  assert_equal None layout.default_root;
  assert_equal 0x280000 (List.assoc "only_root" layout.table_symbols_pa)

let test_default_tables_false_rejects_top_level_mapping _ =
  assert_raises
    (Isla.Page_table_builder.Error
       "page_table: top-level mapping requires an implicit default table, but \
        default_tables = false"
    ) (fun () ->
    ignore
      (make_layout
         [ Isla.Page_table_ast.OptionDefaultTables false;
           Isla.Page_table_ast.Mapping
             { va_name = "x";
               target = Isla.Page_table_ast.PaName "pa_x";
               level = None;
               attrs = []
             }
         ]
      )
  )

let test_default_identity_uses_page_table_arena _ =
  let layout =
    make_layout ~reserved:[0x283000]
      [ Isla.Page_table_ast.IdentityMapping
          {addr = Z.of_int 0x283000; attr = Isla.Page_table_ast.Default}
      ]
  in
  assert_bool "default identity page is tracked as page-table storage"
    (List.mem 0x283000 layout.table_pages)

let test_table_reference_is_validated_but_needs_no_mapping _ =
  let layout =
    make_layout ~reserved:[0x280000; 0x281000]
      [ Isla.Page_table_ast.OptionDefaultTables false;
        table_block Isla.Page_table_ast.S1 "destination" 0x280000
          [ Isla.Page_table_ast.TableRef
              {stage = Isla.Page_table_ast.S2; name = "source"}
          ];
        table_block Isla.Page_table_ast.S2 "source" 0x281000 []
      ]
  in
  assert_equal None layout.default_root;
  assert_bool "both roots share the prebuilt page-table arena mapping"
    (List.length layout.table_entries > 0)

let test_unknown_table_reference_is_rejected _ =
  assert_raises
    (Isla.Page_table_builder.Error "page_table: unknown table root: missing")
    (fun () ->
       ignore
         (make_layout ~reserved:[0x280000]
            [ table_block Isla.Page_table_ast.S1 "destination" 0x280000
                [ Isla.Page_table_ast.TableRef
                    {stage = Isla.Page_table_ast.S2; name = "missing"}
                ]
            ]
         )
  )

let tests =
  "Isla.Page_table_builder"
  >::: [ "materialize physical declaration"
         >:: test_materialize_physical_declaration;
         "mapping alignment is known before data init"
         >:: test_mapping_alignment_is_known_before_data_init;
         "code identity inside reserved block is already satisfied"
         >:: test_code_identity_inside_reserved_block_is_already_satisfied;
         "named and nested roots keep actual addresses"
         >:: test_named_and_nested_roots_keep_actual_addresses;
         "explicit table target keeps actual address"
         >:: test_explicit_table_target_keeps_actual_address;
         "duplicate named root is rejected"
         >:: test_duplicate_named_root_is_rejected;
         "default_tables false uses only named roots"
         >:: test_default_tables_false_uses_only_named_roots;
         "default_tables false rejects top-level mapping"
         >:: test_default_tables_false_rejects_top_level_mapping;
         "default identity uses page-table arena"
         >:: test_default_identity_uses_page_table_arena;
         "table reference is validated but needs no mapping"
         >:: test_table_reference_is_validated_but_needs_no_mapping;
         "unknown table reference is rejected"
         >:: test_unknown_table_reference_is_rejected
       ]

let () = run_test_tt_main tests
