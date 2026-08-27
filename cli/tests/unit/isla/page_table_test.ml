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

(** Unit tests for the Isla page-table setup parser. *)

open OUnit2

let parse input =
  let lexbuf = Lexing.from_string input in
  Isla.Parser.page_table_setup Isla.Lexer.token lexbuf

let parse_binding input =
  let lexbuf = Lexing.from_string input in
  Isla.Parser.binding Isla.Lexer.token lexbuf

let test_default_tables_true _ =
  assert_equal
    [Isla.Page_table_ast.OptionDefaultTables true]
    (parse "option default_tables = true;")

let test_default_tables_false _ =
  assert_equal
    [Isla.Page_table_ast.OptionDefaultTables false]
    (parse "option default_tables = false;")

let test_table_mapping_descriptor_fields _ =
  let expected =
    [ Isla.Page_table_ast.Mapping
        { va_name = "x";
          target = Isla.Page_table_ast.Table (Z.of_int 0x283000);
          attrs = [Isla.Page_table_ast.{name = "APTable"; value = Z.of_int 2}];
          level = Some 2
        }
    ]
  in
  assert_equal expected
    (parse "x |-> table(0x283000) with [APTable=2] at level 2;");
  assert_equal expected
    (parse "x |-> table(0x283000) with [APTable=2] and default at level 2;")

let eval_binding input =
  Isla.Term.eval
    ~lookup_addr:(fun name -> failwith ("unexpected symbol: " ^ name))
    (parse_binding input)

let test_mkdesc_descriptor_fields _ =
  let table_expected =
    Isla.Page_table_desc.table_descriptor 0x283000
    |> fun desc ->
    Isla.Page_table_desc.apply_descriptor_fields desc
      [Isla.Page_table_ast.{name = "APTable"; value = Z.of_int 2}]
    |> Z.of_int64
  in
  assert_equal table_expected (eval_binding "mkdesc2(table=0x283000, APTable=2)");
  let leaf_expected =
    Isla.Page_table_desc.make_descriptor ~level:3 ~oa:0x400000
      ~kind:Isla.Page_table_ast.Data
      ~fields:[Isla.Page_table_ast.{name = "nG"; value = Z.one}]
      ()
    |> Z.of_int64
  in
  assert_equal leaf_expected (eval_binding "mkdesc3(oa=0x400000, nG=1)")

let test_default_identity _ =
  assert_equal
    [ Isla.Page_table_ast.IdentityMapping
        {addr = Z.of_int 0x283000; attr = Isla.Page_table_ast.Default}
    ]
    (parse "identity 0x283000 with default;")

let tests =
  "Isla.Page_table"
  >::: [ "accept default_tables = true" >:: test_default_tables_true;
         "accept default_tables = false" >:: test_default_tables_false;
         "parse table descriptor fields" >:: test_table_mapping_descriptor_fields;
         "evaluate mkdesc descriptor fields" >:: test_mkdesc_descriptor_fields;
         "parse default identity" >:: test_default_identity
       ]

let () = run_test_tt_main tests
