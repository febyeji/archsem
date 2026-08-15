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
(*  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER *)
(*  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,  *)
(*  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,       *)
(*  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR        *)
(*  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    *)
(*  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING      *)
(*  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS        *)
(*  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.              *)
(*                                                                            *)
(******************************************************************************)

let default_capacity = 256

let capacity () =
  match Sys.getenv_opt "ARCHSEM_MEMO_CAPACITY" with
  | Some value -> (
    try max 1 (int_of_string value) with _ -> default_capacity
  )
  | None -> default_capacity

let by_hash eqb =
  let capacity = capacity () in
  let table = Hashtbl.create (min capacity 4096) in
  let order = Queue.create () in
  let cached = ref 0 in
  let evict_one () =
    if !cached >= capacity then begin
      let (old_hash, old_x) = Queue.take order in
      match Hashtbl.find_opt table old_hash with
      | None -> ()
      | Some bucket ->
          let bucket' = Stdlib.List.filter (fun (x', _) -> x' != old_x) bucket in
          if bucket' = [] then Hashtbl.remove table old_hash
          else Hashtbl.replace table old_hash bucket';
          decr cached
    end
  in
  let insert hash x y =
    evict_one ();
    let bucket =
      match Hashtbl.find_opt table hash with None -> [] | Some bucket -> bucket
    in
    Hashtbl.replace table hash ((x, y) :: bucket);
    Queue.add (hash, x) order;
    incr cached
  in
  fun x thunk ->
    let hash = Hashtbl.hash x in
    match Hashtbl.find_opt table hash with
    | None ->
        let y = thunk () in
        insert hash x y; y
    | Some bucket -> (
      match Stdlib.List.find_opt (fun (x', _) -> eqb x x') bucket with
      | Some (_, y) -> y
      | None ->
          let y = thunk () in
          insert hash x y; y
    )
