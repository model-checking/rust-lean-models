-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
import RustLeanModels.Basic
import Lean
open List
open Mathlib
open Nat
open Char
set_option maxHeartbeats 10000000


/-
next

How to translate:
Rust: let x = s.next()
Lean: let x:= s.next.1
      let s:= s.next.2

-/

namespace Iterator

def next (s: List a) : (Option a) × List a := match s with
  | [] => (none , [])
  | h::t => (some h, t)

/-
peek
-/

def peek (s: List a) : Option a := match s with
  | [] => none
  | _::[] => none
  | _::h1::_ => some h1

/-
flatten
From: core::iter::adapers::flatten
-/

def flatten (s: List (List a)):= List.foldl List.append [] s

lemma fold_append_cons: List.foldl List.append (v::u) s = v:: List.foldl List.append u s :=by
  induction s generalizing v u; simp only [foldl_nil]
  rename_i h t ind;
  simp only [foldl_cons, append_eq, cons_append]; rw[ind]

lemma fold_append_para1_elim : List.foldl List.append u l = u ++ (List.foldl List.append [] l) :=by
  induction l generalizing u
  simp only [foldl_nil, List.append_nil]
  rename_i h t ind ;
  simp only [foldl_cons, append_eq, List.nil_append]
  rw[@ind (u++h), @ind h]; simp only [List.append_assoc]


lemma flatten_cons : flatten (h::t) = h ++ flatten t :=by
  unfold flatten ; simp only [foldl_cons, append_eq, List.nil_append]
  rw[fold_append_para1_elim]

lemma flatten_append : flatten (l1 ++ l2) = flatten l1 ++ flatten l2 :=by
  induction l1 generalizing l2
  simp only [flatten, List.nil_append, foldl_nil]
  rename_i h t ind
  have: h :: t ++ l2 = h::(t++l2) := by simp only [cons_append]
  simp only [this, flatten_cons, ind, List.append_assoc]

end Iterator
