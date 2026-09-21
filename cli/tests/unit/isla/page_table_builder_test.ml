(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      The ArchSem contributors                                             *)
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
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR     *)
(*  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT      *)
(*  HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,     *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED  *)
(*  TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR    *)
(*  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(*  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING      *)
(*  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(*  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.              *)
(*                                                                            *)
(******************************************************************************)

open OUnit2
module Ast = Isla.Page_table_ast

let mapping target = Ast.Mapping {va_name = "x"; target; attrs = []; level = None}

let table_mapping addr =
  Ast.Mapping
    { va_name = "x";
      target = Ast.Table (Isla.Term.Const (Z.of_int addr));
      attrs = [];
      level = Some 2
    }

let table_block name base body =
  Ast.TableBlock {stage = Ast.S1; name; base = Z.of_int base; body}

let test_explicit_table_pages_are_reserved _ =
  let state = Isla.Eval_state.create () in
  Isla.Eval_state.add_virtual state "x" 0x400000;
  let symbol_allocator = Isla.Allocator.make ~base:0x400000 () in
  let table_allocator =
    Isla.Allocator.make ~base:0x200000 ~limit:0x400000
      ~reserved:[0x280000; 0x2c0000] ()
  in
  let stmts =
    [ Ast.Physical ["pa1"];
      table_block "old_l3" 0x280000
        [table_mapping 0x283000; mapping (Ast.PaName "pa1")];
      table_block "new_l3" 0x2c0000
        [table_mapping 0x2c3000; mapping (Ast.PaName "pa1")]
    ]
  in
  ignore
    (Isla.Page_table_builder.build ~arch:Litmus.Arch_id.Arm ~symbol_allocator
       ~table_allocator ~table_block:0x200000 ~state stmts
    )

let tests =
  "Isla.Page_table_builder"
  >::: [ "explicit table pages are reserved"
         >:: test_explicit_table_pages_are_reserved
       ]

let () = run_test_tt_main tests
