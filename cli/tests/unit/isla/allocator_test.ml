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
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A   *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER  *)
(*  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,   *)
(*  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(*  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(*  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(*  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(*  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(*  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.              *)
(*                                                                            *)
(******************************************************************************)

open OUnit2
open Isla

let int = string_of_int

let test_regions_are_scoped _ =
  let allocator =
    Allocator.make_in_regions
      [ {base = 0x200000; size = Allocator.big_size};
        {base = 0x600000; size = Allocator.big_size}
      ]
  in
  assert_equal ~printer:int 0x200000 (Allocator.alloc_page allocator);
  for _ = 1 to 511 do
    ignore (Allocator.alloc_page allocator)
  done;
  assert_equal ~printer:int 0x600000 (Allocator.alloc_page allocator)

let test_reserved_page_is_skipped _ =
  let allocator =
    Allocator.make_in_regions ~reserved:[0x201234]
      [{base = 0x200000; size = Allocator.big_size}]
  in
  assert_equal ~printer:int 0x200000 (Allocator.alloc_page allocator);
  assert_equal ~printer:int 0x202000 (Allocator.alloc_page allocator)

let test_big_allocation_skips_reserved_block _ =
  let allocator =
    Allocator.make_in_regions ~reserved:[0x1400] [{base = 0; size = 1 lsl 30}]
  in
  assert_equal ~printer:int 0x200000 (Allocator.alloc_big allocator)

let test_regions_exhaust _ =
  let allocator =
    Allocator.make_in_regions [{base = 0x4000; size = Allocator.page_size}]
  in
  ignore (Allocator.alloc_page allocator);
  assert_raises (Failure "allocator: regions exhausted") (fun () ->
    ignore (Allocator.alloc_page allocator)
  )

let tests =
  "Isla.Allocator"
  >::: [ "regions are scoped" >:: test_regions_are_scoped;
         "reserved page is skipped" >:: test_reserved_page_is_skipped;
         "big allocation skips reserved block"
         >:: test_big_allocation_skips_reserved_block;
         "regions exhaust" >:: test_regions_exhaust
       ]

let () = run_test_tt_main tests
