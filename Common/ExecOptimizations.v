(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2026                                                        *)
(*      Yeji Han, Seoul National University                                   *)
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

(** Exact-order specifications for the execution enumeration optimizations. *)

Require Import Options.
Require Import Common.
Require Import Effects.
Require Import Exec.

Import Exec.

Definition merge_all {E A B} (f : A → res E B) (l : list A) :=
  foldr merge (make [] []) (map f l).

Lemma merge_assoc {E A} (e1 e2 e3 : res E A) :
  merge e1 (merge e2 e3) = merge (merge e1 e2) e3.
Proof.
  destruct e1, e2, e3.
  unfold merge. cbn.
  rewrite !List.app_assoc.
  done.
Qed.

Lemma merge_all_app {E A B} (f : A → res E B) l1 l2 :
  merge_all f (l1 ++ l2) = merge (merge_all f l1) (merge_all f l2).
Proof.
  induction l1 as [|x l1 IH].
  - change (merge_all f l2 = merge (make [] []) (merge_all f l2)).
    destruct (merge_all f l2). done.
  - change
      (merge (f x) (merge_all f (l1 ++ l2)) =
       merge (merge (f x) (merge_all f l1)) (merge_all f l2)).
    rewrite IH.
    apply merge_assoc.
Qed.

Lemma merge_all_concat_map {E A B C}
    (f : B → res E C) (g : A → list B) l :
  merge_all f (List.concat (map g l)) =
  merge_all (λ x, merge_all f (g x)) l.
Proof.
  induction l as [|x l IH].
  - done.
  - change
      (merge_all f (g x ++ List.concat (map g l)) =
       merge (merge_all f (g x))
         (merge_all (λ x, merge_all f (g x)) l)).
    rewrite merge_all_app, IH.
    done.
Qed.

Lemma choosel_bind_spec {A St E B} (l : list A)
    (f : A → t St E B) st :
  ((choosel l ≫= f) st) = merge_all (λ x, f x st) l.
Proof.
  unfold mbind, mbind_inst.
  unfold choosel.
  rewrite map_tail_eq_map.
  unfold mbind, res_mbind_inst.
  rewrite res_mbind_tail_eq_foldr.
  cbn.
  rewrite List.map_map.
  done.
Qed.

Lemma choose_list_cont_spec {A St E B} (l : list A)
    (f : A → t St E B) :
  choose_list_cont l f = (choosel l ≫= f).
Proof.
  apply functional_extensionality. intro st.
  unfold choose_list_cont.
  rewrite res_mbind_tail_eq_foldr.
  rewrite choosel_bind_spec.
  done.
Qed.

Lemma merge_all_map {E A B C}
    (f : B → res E C) (g : A → B) l :
  merge_all f (map g l) = merge_all (λ x, f (g x)) l.
Proof.
  induction l as [|x l IH].
  - done.
  - change
      (merge (f (g x)) (merge_all f (map g l)) =
       merge (f (g x)) (merge_all (λ x, f (g x)) l)).
    rewrite IH.
    done.
Qed.

Lemma choosel_map_bind {A B St E C}
    (g : A → B) (l : list A) (f : B → t St E C) :
  (choosel (map g l) ≫= f) =
  (choosel l ≫= λ x, f (g x)).
Proof.
  apply functional_extensionality. intro st.
  rewrite !choosel_bind_spec.
  apply merge_all_map.
Qed.

Lemma choosel_concat_map_bind {A B St E C}
    (g : A → list B) (l : list A) (f : B → t St E C) :
  (choosel (List.concat (map g l)) ≫= f) =
  (choosel l ≫= λ x, choosel (g x) ≫= f).
Proof.
  apply functional_extensionality. intro st.
  rewrite !choosel_bind_spec.
  rewrite merge_all_concat_map.
  f_equal.
  apply functional_extensionality. intro x.
  symmetry.
  apply choosel_bind_spec.
Qed.

Lemma list_fmap_eq_map {A B} (f : A → B) l :
  (f <$> l : list B) = map f l.
Proof.
  induction l as [|x l IH].
  - done.
  - cbn. rewrite IH. done.
Qed.

Lemma cprodn_cons_as_concat {A n}
    (h : list A) (choices : vec (list A) n) :
  cprodn (h ::: choices) =
  List.concat
    (map (λ x, map (λ xs, x ::: xs) (cprodn choices)) h).
Proof.
  change
    (((λ '(a, b), a ::: b) <$> cprod h (cprodn choices)) =
     List.concat
       (map (λ x, map (λ xs, x ::: xs) (cprodn choices)) h)).
  rewrite list_fmap_eq_map.
  rewrite list_cprod_list_prod.
  induction h as [|x h IH].
  - done.
  - cbn [List.list_prod].
    rewrite List.map_app, IH.
    f_equal.
    rewrite List.map_map.
    done.
Qed.

Lemma choose_cprodn_cont_spec {A St E R n}
    (choices : vec (list A) n)
    (k : vec A n → t St E R) :
  choose_cprodn_cont choices k =
  (xs ← choosel (cprodn choices); k xs).
Proof.
  dependent induction choices.
  - apply functional_extensionality. intro st.
    cbn [choose_cprodn_cont cprodn].
    unfold mbind, mbind_inst, choosel.
    rewrite map_tail_eq_map.
    unfold mbind, res_mbind_inst.
    rewrite res_mbind_tail_eq_foldr.
    cbn.
    destruct (k [#] st).
    unfold merge. cbn.
    rewrite !List.app_nil_r.
    done.
  - cbn [choose_cprodn_cont cprodn].
    rewrite choose_list_cont_spec.
    assert
      (Hrec :
        (λ x,
          choose_cprodn_cont choices
            (λ xs : vec A n, k (x ::: xs))) =
        (λ x,
          choosel (cprodn choices) ≫=
            λ xs : vec A n, k (x ::: xs))).
    {
      apply functional_extensionality. intro x.
      apply IHchoices.
    }
    rewrite Hrec.
    change
      ((choosel h ≫=
          λ x,
            choosel (cprodn choices) ≫=
              λ xs : vec A n, k (x ::: xs)) =
       (choosel (cprodn (h ::: choices)) ≫= k)).
    rewrite cprodn_cons_as_concat.
    rewrite choosel_concat_map_bind.
    assert
      (Hmap :
        (λ x,
          choosel (cprodn choices) ≫=
            λ xs : vec A n, k (x ::: xs)) =
        (λ x,
          choosel
            (map (λ xs : vec A n, x ::: xs) (cprodn choices)) ≫= k)).
    {
      apply functional_extensionality. intro x.
      symmetry.
      apply choosel_map_bind.
    }
    rewrite Hmap.
    done.
Qed.
