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

let parse input =
  Isla.Parser.page_table_setup Isla.Lexer.token (Lexing.from_string input)

let test_default_identity _ =
  assert_equal
    [ Isla.Page_table_ast.IdentityMapping
        { addr = Isla.Term.Const (Z.of_int 0x283000);
          attr = Isla.Page_table_ast.Default
        }
    ]
    (parse "identity 0x283000 with default;")

let eval_binding input =
  let term = Isla.Parser.binding Isla.Lexer.token (Lexing.from_string input) in
  Isla.Term.eval ~state:(Isla.Eval_state.create ()) term

let test_ng_descriptor_field _ =
  assert_equal (Z.of_int 0x400c43) (eval_binding "mkdesc3(oa=0x400000, nG=1)")

let test_table_descriptor_field _ =
  let expected = Z.of_string "0x4000000000283003" in
  assert_equal expected (eval_binding "mkdesc2(table=0x283000, APTable=2)")

let test_table_mapping_descriptor_field _ =
  assert_equal
    [ Isla.Page_table_ast.Mapping
        { va_name = "x";
          target = Isla.Page_table_ast.Table (Isla.Term.Const (Z.of_int 0x283000));
          attrs = [{name = "APTable"; value = Isla.Term.Const (Z.of_int 2)}];
          level = Some 2
        }
    ]
    (parse "x |-> table(0x283000) with [APTable=2] at level 2;")

let test_table_reference _ =
  assert_equal
    [Isla.Page_table_ast.TableRef {stage = Isla.Page_table_ast.S1; name = "other"}]
    (parse "s1table other;")

let tests =
  "Isla.Page_table"
  >::: [ "parse default identity" >:: test_default_identity;
         "evaluate nG descriptor field" >:: test_ng_descriptor_field;
         "evaluate table descriptor field" >:: test_table_descriptor_field;
         "parse table mapping descriptor field"
         >:: test_table_mapping_descriptor_field;
         "parse table reference" >:: test_table_reference
       ]

let () = run_test_tt_main tests
