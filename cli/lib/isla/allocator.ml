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

(** Region-scoped address allocator. *)

type region =
  { base : int;
    size : int
  }

type bounds =
  { base : int;
    limit : int option
  }

type t =
  { mutable regions : bounds list;
    mutable current : int;
    reserved_pages : int list
  }

let default_base = 0x1000

let page_size = 0x1000

let big_size = 1 lsl 21

let align_up addr alignment =
  if alignment <= 0 then
    Litmus.Error.failwith "allocator: alignment must be positive";
  let rem = addr mod alignment in
  if rem = 0 then addr
  else
    let delta = alignment - rem in
    if addr > max_int - delta then
      Litmus.Error.failwith "allocator: address overflow"
    else addr + delta

let page_after addr = align_up (addr + 1) page_size

let reserved_pages reserved =
  List.map (fun addr -> addr - (addr mod page_size)) reserved
  |> List.sort_uniq Int.compare

let make ?(base = default_base) ?(reserved = []) () =
  if base < 0 then Litmus.Error.failwith "allocator: base must be non-negative";
  { regions = [{base; limit = None}];
    current = base;
    reserved_pages = reserved_pages reserved
  }

let checked_bound {base; size} =
  if base < 0 then
    Litmus.Error.failwith "allocator: region base must be non-negative";
  if size <= 0 then
    Litmus.Error.failwith "allocator: region size must be positive";
  if base > max_int - size then
    Litmus.Error.failwith "allocator: region overflows";
  {base; limit = Some (base + size)}

let check_non_overlapping regions =
  let rec check = function
    | [] | [_] -> ()
    | {limit = Some limit; _} :: ({base; _} :: _ as rest) ->
        if limit > base then Litmus.Error.failwith "allocator: regions overlap";
        check rest
    | _ -> assert false
  in
  check regions

let make_in_regions ?(reserved = []) regions =
  let regions =
    List.map checked_bound regions
    |> List.sort (fun a b -> Int.compare a.base b.base)
  in
  if regions = [] then Litmus.Error.failwith "allocator: no regions provided";
  check_non_overlapping regions;
  { regions;
    current = (List.hd regions).base;
    reserved_pages = reserved_pages reserved
  }

let overlapping_reserved_page allocator start stop =
  List.find_opt
    (fun page -> page < stop && page + page_size > start)
    allocator.reserved_pages

let fits limit addr size =
  addr <= max_int - size
  && match limit with None -> true | Some limit -> addr <= limit - size

let rec alloc_aligned allocator ~size ~alignment =
  if size <= 0 then Litmus.Error.failwith "allocator: size must be positive";
  match allocator.regions with
  | [] -> Litmus.Error.failwith "allocator: regions exhausted"
  | region :: remaining -> (
      let current = max allocator.current region.base in
      let addr = align_up current alignment in
      if not (fits region.limit addr size) then (
        allocator.regions <- remaining;
        match remaining with
        | [] -> alloc_aligned allocator ~size ~alignment
        | next :: _ ->
            allocator.current <- next.base;
            alloc_aligned allocator ~size ~alignment
      )
      else
        let stop = addr + size in
        match overlapping_reserved_page allocator addr stop with
        | Some page ->
            allocator.current <- page_after page;
            alloc_aligned allocator ~size ~alignment
        | None ->
            allocator.current <- stop;
            addr
    )

let alloc_page allocator =
  alloc_aligned allocator ~size:page_size ~alignment:page_size

let alloc_big allocator =
  alloc_aligned allocator ~size:big_size ~alignment:big_size
