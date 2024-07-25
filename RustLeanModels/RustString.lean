-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
import RustLeanModels.Basic
import RustLeanModels.Iterator
import Lean
open List
open Mathlib
open Nat
open Char
open Iterator
set_option maxHeartbeats 10000000

/-
Variable naming conventions:
-Assumptions (Prop): starts with g  (I save h for h::t)
-Strings (Str): s, s1, s2, (h::t)
-Substrings (Str): ss
-Prefixes (Str): p p1 p2
-Characters (Char): c
-Patterns: P
-Char filters (Char → Bool): f
-Positions, Indexes (Nat) : i j
-Words (members of a split) (Str) : w
-General Nats: m n
-Lists Nat: l
-Elements of list, inputs of function: x
-Extra parameters in aux functions: k
-/

namespace RustString


--There are 5 ascii whitespace characters in Rust function is_ascii_whitespace
--but only 4 in Lean function isWhitespace
def is_ascii_whitespace (c : Char) := (isWhitespace c) || (c = '\x0C')


/-
Function: is_whitespace
From: core::char::is_whitespace
Description: https://doc.rust-lang.org/std/primitive.char.html#method.is_whitespace
-/

def is_whitespace (c : Char): Bool :=
  c.val ∈ [9, 10, 11, 12, 13, 32, 133, 160, 5760,
          8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202,
          8232, 8233, 8239, 8287, 12288]

def Char_is_ascii (c : Char) : Bool := c.val ≤ 127

/-
All iterator's functions are implemented directly on Str

chars => s.chars() = s

-/

/-
Function: byteSize
From: core::str::len
Description: https://doc.rust-lang.org/std/primitive.str.html#method.len
-/
def sum_list_Nat (l : List Nat) := List.foldl Nat.add 0 l

lemma fold_add_para1_elim: List.foldl Nat.add x l = x + List.foldl Nat.add 0 l := by
  induction l generalizing x
  simp only [foldl_nil, add_zero]
  rename_i h t ind
  simp only [foldl_cons, add_eq, zero_add] ; rw[@ind h, @ind (x+h)]; omega

lemma sum_List_Nat_cons : sum_list_Nat (h::t) = h + sum_list_Nat t  :=by
  simp only [sum_list_Nat, foldl_cons, add_eq, zero_add]
  exact fold_add_para1_elim


@[simp]
def byteSize (s : List Char) : Nat := match s with
  | [] => 0
  | h::t => Char.utf8Size h + byteSize t


def byteSize_def (s : List Char) : Nat := sum_list_Nat (List.map (fun x: Char => Char.utf8Size x) s)


lemma byteSize_EQ : byteSize s = byteSize_def s :=by
  induction s
  simp only [byteSize, byteSize_def, sum_list_Nat, map_nil, foldl_nil]
  rename_i h t ind
  simp only [byteSize, byteSize_def, map_cons]
  rw[sum_List_Nat_cons, ← byteSize_def, ← ind]


@[simp]
def byteSize_aux (s : Str) (k : Nat)  : Nat := match s with
  | [] => k
  | h::t => byteSize_aux t (k + Char.utf8Size h)

lemma byteSize_aux_para1_le : i ≤ byteSize_aux p i :=by
  induction p generalizing i;
  unfold byteSize_aux; simp
  unfold byteSize_aux
  rename_i h t ind
  have : i + Char.utf8Size h ≤ byteSize_aux t (i + Char.utf8Size h):= by apply ind
  linarith

lemma byteSize_aux_para1_add : byteSize_aux p i  = i + byteSize_aux p 0:=by
  induction p generalizing i;
  simp; simp; rename_i h t ind
  have e1: byteSize_aux t (i + Char.utf8Size h) = (i + Char.utf8Size h) + byteSize_aux t 0 := ind
  have e2: byteSize_aux t (Char.utf8Size h) =  Char.utf8Size h + byteSize_aux t 0 := ind
  rw[e1,e2] ; apply add_assoc

lemma byteSize_aux_para1_elim: byteSize s = byteSize_aux s 0 := by
  induction s
  simp only [byteSize, byteSize_aux]
  rename_i h t ind
  simp only [byteSize, byteSize_aux, zero_add]
  rw[byteSize_aux_para1_add, ind];

lemma byteSize_ge_csize_head : byteSize (h::t) ≥ Char.utf8Size h := by
  simp only [byteSize, ge_iff_le, le_add_iff_nonneg_right, _root_.zero_le]

@[simp]
lemma byteSize_cons : byteSize (h::t) = (Char.utf8Size h) + byteSize t :=by
  simp only [byteSize]


@[simp]
lemma byteSize_concat : byteSize (s1 ++ s2) = byteSize (s1) + byteSize (s2) :=by
  induction s1; simp only [byteSize, List.nil_append, zero_add]
  rename_i h t ind
  have: h :: t ++ s2 =  h :: (t ++ s2) := by simp only [cons_append]
  rw[this,byteSize_cons, ind, byteSize_cons]; linarith

@[simp]
lemma byteSize_reverse : byteSize (reverse s) = byteSize s :=by
  induction s; simp only [byteSize]
  rename_i h t ind;
  have: reverse (h :: t) = reverse t ++ [h] :=by simp only [reverse_cons]
  rw[byteSize_cons, this, byteSize_concat, ind];
  simp only [byteSize, zero_add]; linarith

lemma nil_of_byteSize_zero : byteSize s = 0 → s = [] := by
  cases s; simp only [implies_true]
  simp only [byteSize_cons, add_eq_zero, not_false_eq_true, not_sym, and_imp, imp_false]
  rename_i h _ ; have : Char.utf8Size h > 0 := by apply Char.utf8Size_pos
  intro; omega

def ListCharPos_aux (s: Str) (i: Nat):= match s with
  | [] => []
  | h::t => match t with
            | [] => [i]
            | _::_ => i:: ListCharPos_aux t (i+ Char.utf8Size h)

/- List of the byte positions of all Chars in the String s-/
def ListCharPos (s: Str) := ListCharPos_aux s 0

lemma ListCharPos_aux_sound : x ∈ ListCharPos_aux s k ↔ ∃ p, List.IsPrefix p s ∧ p ≠ s ∧ byteSize p + k = x :=by
  induction s generalizing k
  simp only [ListCharPos_aux, not_mem_nil, prefix_nil, ne_eq, exists_eq_left, not_true_eq_false,
    byteSize, zero_add, false_and]
  rename_i h t ind
  simp only [ListCharPos_aux, ne_eq]
  cases t; simp only [mem_singleton]
  constructor;
  intro g; use [];
  simp only [_root_.nil_prefix, not_false_eq_true, not_sym, byteSize, ← g, zero_add, and_self]
  intro gp; obtain ⟨p, gp⟩:= gp;
  cases p; simp only [_root_.nil_prefix, not_false_eq_true, not_sym, byteSize, zero_add, true_and] at gp; symm; exact gp
  rename_i hp tp; simp only [cons.injEq, not_and, byteSize] at gp
  have g:= prefix_cons gp.left; have g1:=gp.right.left g.left;
  simp only [prefix_nil, g1, not_false_eq_true, not_sym, and_false] at g
  rename_i ht tt; simp only [mem_cons];
  constructor; intro g; cases g; use [];
  simp only [_root_.nil_prefix, not_false_eq_true, not_sym, byteSize, zero_add, true_and]; symm; assumption
  simp only [ne_eq, not_false_eq_true, not_sym,true_implies] at ind; rename_i gm
  have ind:= (@ind (k + h.utf8Size)).mp gm; obtain ⟨p, gp⟩:=ind
  use (h::p); simp only [prefix_cons_inj, gp, cons.injEq, and_false, not_false_eq_true, not_sym,byteSize, true_and]
  omega
  intro gp; obtain ⟨p, gp⟩:=gp; cases p;
  simp only [_root_.nil_prefix, not_false_eq_true, not_sym, byteSize, zero_add, true_and] at gp
  simp only [← gp, ListCharPos_aux, true_or]
  rename_i hp tp; simp only [cons.injEq, not_and, byteSize] at gp
  have : ∃ p, p <+: ht :: tt ∧ p ≠ ht :: tt ∧ byteSize p + (k + h.utf8Size) = x:= by
    use tp; have g:= prefix_cons gp.left;
    simp only [g, ne_eq, gp.right.left g.left, not_false_eq_true, not_sym, true_and]; rw[← g.left]; omega
  simp only [ne_eq, not_false_eq_true, not_sym, true_implies] at ind;
  simp only [ind.mpr this, or_true]

theorem ListCharPos_sound : x ∈ ListCharPos s ↔ ∃ p, List.IsPrefix p s ∧ p ≠ s ∧ byteSize p = x :=by
  simp only [ListCharPos, ListCharPos_aux_sound, ne_eq, add_zero]


def CharBoundPos_aux (l: Str) (s: Nat): List Nat := match l with
  | [] => [s]
  | h::t => s :: CharBoundPos_aux t (s + Char.utf8Size h)

/- List of the char boundary positions of the String s.
  The list includes the byte positions of all Chars (ListCharPos) and the length in bytes (byteSize) of s.
-/
@[simp]
def CharBoundPos (s: Str) : List Nat := CharBoundPos_aux s 0

def CharBoundPos_def (s: Str):= (ListCharPos s)++[byteSize s]

-- lemmas
lemma CharBoundPos_aux_para1_add: CharBoundPos_aux s (a+b) = List.map (fun x => x + a) (CharBoundPos_aux s b) :=by
  induction s generalizing a b
  simp only [CharBoundPos_aux, map_cons, map_nil, cons.injEq, and_true]; omega
  rename_i h t ind
  simp only [CharBoundPos_aux, map_cons, cons.injEq]
  constructor; omega; rw[add_assoc]; exact ind

lemma CharBoundPos_aux_para1_elim: CharBoundPos_aux s k = List.map (fun x => x + k) (CharBoundPos s) :=by
  unfold CharBoundPos
  have : k = k + 0 := by simp only [add_zero]
  rw(config:={occs:=.pos [1]}) [this]; exact CharBoundPos_aux_para1_add

lemma ListCharPos_length_aux : (ListCharPos_aux s k).length = s.length := by
  induction s generalizing k ; simp [ListCharPos_aux]
  rename_i head tail ind
  simp only [ListCharPos_aux, length_cons]
  split; simp only [List.length_singleton, length_nil, reduceSucc]; rename_i tt h ht;
  simp_all only [ListCharPos_aux, length_cons]


lemma ListCharPos_length : (ListCharPos s).length = s.length :=by
  unfold ListCharPos; apply ListCharPos_length_aux

lemma CharBoundPos_length_aux: (CharBoundPos_aux s k).length = s.length + 1 := by
  induction s generalizing k; unfold CharBoundPos_aux;
  simp_all only [List.length_singleton, length_nil, zero_add]
  rename_i h t ind
  unfold CharBoundPos_aux;
  simp only [zero_add, length_cons, succ.injEq]
  simp_all only

lemma CharBoundPos_length: (CharBoundPos s).length = s.length + 1 := by
  unfold CharBoundPos; apply CharBoundPos_length_aux

lemma ListCharPos_prefix_CharBoundPos_aux : List.IsPrefix (ListCharPos_aux s k) (CharBoundPos_aux s k) := by
  generalize hl: s.length = l
  induction l generalizing s k
  have : s= [] := by apply List.eq_nil_of_length_eq_zero hl
  unfold ListCharPos_aux CharBoundPos_aux
  simp_all only [length_nil, zero_eq]; apply List.nil_prefix
  rename_i n ind
  unfold ListCharPos_aux CharBoundPos_aux
  cases s; simp_all only [length_nil, not_false_eq_true, not_sym]
  rename_i head tail; simp only
  cases tail; simp only; unfold List.IsPrefix; use CharBoundPos_aux [] (k + Char.utf8Size head);
  simp only [CharBoundPos_aux,singleton_append];
  simp only [ListCharPos_aux, CharBoundPos_aux]; rename_i h1 t1
  apply (List.prefix_cons_inj k).mpr;
  have : (head :: h1 :: t1).length = succ (h1 :: t1).length := by simp only [length_cons]
  rw[this] at hl; simp only  [succ.injEq] at hl;
  exact ind hl

lemma ListCharPos_prefix_CharBoundPos: List.IsPrefix (ListCharPos s) (CharBoundPos s) := by
  unfold CharBoundPos ListCharPos; apply ListCharPos_prefix_CharBoundPos_aux

lemma byteSize_aux_t0 : ∀ h >0, byteSize_aux s (i + h)  > i := by
  induction s ;
  unfold byteSize_aux; simp only [gt_iff_lt, lt_add_iff_pos_right, imp_self, forall_const];
  unfold byteSize_aux; rename_i h1 t1 ind
  intro h hm
  have : (i + h + Char.utf8Size h1) = i + (h + Char.utf8Size h1) := by linarith
  simp_all only [gt_iff_lt, add_pos_iff, true_or]

lemma byteSize_gt_ListCharPos_aux: ∀ x ∈ (ListCharPos_aux s k), byteSize_aux s k > x := by
  generalize hl : s.length = l
  induction l generalizing k s
  have : s = [] := by apply List.eq_nil_of_length_eq_zero hl
  simp only [this, ListCharPos_aux, not_mem_nil, byteSize_aux, gt_iff_lt, IsEmpty.forall_iff, forall_const]
  rename_i n ind
  unfold ListCharPos_aux byteSize_aux
  split; simp only [not_mem_nil, gt_iff_lt, IsEmpty.forall_iff, forall_const];
  rename_i l h t; split; simp only [mem_singleton, byteSize_aux, gt_iff_lt, forall_eq, lt_add_iff_pos_right]
  have : Char.utf8Size h > 0 :=by apply Char.utf8Size_pos
  linarith
  rename_i t head tail
  intro x hx; simp only [mem_cons] at hx; cases hx
  rename_i hx
  unfold byteSize_aux
  have : byteSize_aux tail (k + Char.utf8Size h + Char.utf8Size head) > x := by
    rw[hx] ;
    have : k + Char.utf8Size h + Char.utf8Size head = k + (Char.utf8Size h + Char.utf8Size head) := by linarith
    rw[this]; apply byteSize_aux_t0;
    have : Char.utf8Size h > 0 := by apply Char.utf8Size_pos
    linarith
  assumption
  have : (h:: head :: tail).length = succ (head::tail).length := by simp only [length_cons]
  simp only [this, succ.injEq] at hl
  simp_all only [gt_iff_lt, length_cons];

lemma byteSize_gt_ListCharPos: ∀ x ∈ (ListCharPos s), byteSize s > x :=by
  unfold ListCharPos; rw[byteSize_aux_para1_elim]; apply byteSize_gt_ListCharPos_aux

lemma byteSize_aux_mem_CharBoundPos_aux : (byteSize_aux s k) ∈ (CharBoundPos_aux s k) := by
  induction s generalizing k ;
  simp only [byteSize_aux, CharBoundPos_aux, mem_singleton]
  rename_i head tail ind
  unfold byteSize_aux CharBoundPos_aux
  have : (byteSize_aux tail (k + Char.utf8Size head)) ∈  (CharBoundPos_aux tail (k + Char.utf8Size head)) := by
    apply ind
  simp_all only [elem_eq_mem, decide_eq_true_eq, decide_True, mem_cons, or_true]

lemma byteSize_in_CharBoundPos :  (byteSize s) ∈  (CharBoundPos s) := by
  unfold CharBoundPos; rw[byteSize_aux_para1_elim]
  apply byteSize_aux_mem_CharBoundPos_aux

theorem CharBoundPos_EQ : CharBoundPos s = CharBoundPos_def s := by
  unfold CharBoundPos_def
  have p: List.IsPrefix (ListCharPos s) (CharBoundPos s) := by exact ListCharPos_prefix_CharBoundPos
  unfold List.IsPrefix at p; obtain ⟨t, ht⟩ := p
  have m:  byteSize s ∈ CharBoundPos s := by exact byteSize_in_CharBoundPos
  have tl: t.length = 1 := by
    have e1: (CharBoundPos s).length = s.length +1 := by apply CharBoundPos_length
    have e2: (ListCharPos s).length = s.length := by apply ListCharPos_length
    have e3: (ListCharPos s ++ t).length = (ListCharPos s).length + t.length := by simp only [ListCharPos, length_append]
    simp_all only [ListCharPos, CharBoundPos, byteSize, add_right_inj]
  rw [← ht] at m; simp only [byteSize, ListCharPos, mem_append] at m
  have g: ∀ m ∈ (ListCharPos s), byteSize s > m := byteSize_gt_ListCharPos
  have g0: ∀ m ∈ (ListCharPos s), byteSize s ≠ m := by
    intro m hm;
    have : byteSize s > m := by simp_all only [ListCharPos, CharBoundPos, byteSize, gt_iff_lt]
    linarith
  have: (byteSize s ∉ ListCharPos s) :=by apply not_in_forall_not_eq g0
  simp only [byteSize, ListCharPos] at this
  simp only [this, false_or] at m
  cases t; simp only [not_mem_nil] at m; rename_i a b
  cases b; simp_all only [ListCharPos, byteSize, gt_iff_lt, ne_eq, CharBoundPos, List.length_singleton,
    mem_singleton]; rename_i htl ttl
  simp only [length_cons, succ.injEq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    not_sym] at tl

lemma prefix_byteSize_in_CharBoundPos: List.IsPrefix p s → byteSize p ∈ CharBoundPos s :=by
  rw[CharBoundPos_EQ, CharBoundPos_def]; intro g;
  by_cases (p ≠ s)
  have: byteSize p ∈ ListCharPos s :=by apply ListCharPos_sound.mpr; use p;
  simp only [mem_append, this, mem_singleton, true_or]
  rename_i gc; simp only [ne_eq, Decidable.not_not] at gc
  simp only [gc, mem_append, mem_singleton, or_true]

lemma prefix_byteSize_le_aux  (g: List.IsPrefix p s) : byteSize_aux p k ≤ byteSize_aux s k:=by
  generalize gl: s.length = n
  induction n generalizing p k s
  have : s =[] := by apply List.eq_nil_of_length_eq_zero gl
  simp_all only [prefix_nil, length_nil, zero_eq, le_refl]
  rename_i n ind
  cases s; simp_all only [prefix_nil, length_nil, not_false_eq_true, not_sym]
  cases p;
  rename_i head tail; unfold byteSize_aux
  have : k + Char.utf8Size head ≤ byteSize_aux tail (k + Char.utf8Size head):= by apply byteSize_aux_para1_le
  linarith
  rename_i hp tp hs ts
  have := prefix_cons g
  simp_all only [length_cons, succ.injEq, byteSize_aux]

lemma prefix_byteSize_le (h: List.IsPrefix p s) : byteSize p  ≤ byteSize s :=by
  rw[byteSize_aux_para1_elim]; rw[byteSize_aux_para1_elim]; apply prefix_byteSize_le_aux h

lemma prefix_byteSize_lt_aux  (g: List.IsPrefix p s) (gl: p.length < s.length): byteSize_aux p k < byteSize_aux s k:=by
  generalize gn: s.length = n
  induction n generalizing p k s
  have : s =[] := by apply List.eq_nil_of_length_eq_zero gn
  simp_all only [prefix_nil, length_nil, lt_self_iff_false]
  rename_i n ind
  cases s; simp_all only [prefix_nil, lt_self_iff_false]
  cases p;
  rename_i head tail; unfold byteSize_aux
  have : k + Char.utf8Size head ≤  byteSize_aux tail (k + Char.utf8Size head):= by apply byteSize_aux_para1_le
  have : Char.utf8Size head > 0 :=by apply Char.utf8Size_pos
  linarith
  rename_i hs ts hp tp
  have g := prefix_cons g
  simp_all only [length_cons, succ.injEq, byteSize_aux, gt_iff_lt]
  apply ind g.right (by omega) gn

lemma prefix_byteSize_lt (g: List.IsPrefix p s) (gp: p.length < s.length): byteSize p  < byteSize s :=by
  rw[byteSize_aux_para1_elim]; rw[byteSize_aux_para1_elim]; apply prefix_byteSize_lt_aux g gp

lemma length_le_of_byteSize_le (g1: List.IsPrefix p1 s) (g2: List.IsPrefix p2 s)
   (hi: byteSize p1 ≤ byteSize p2) : p1.length ≤ p2.length :=by
  by_contra
  simp_all only [byteSize, not_le]
  have : List.IsPrefix p2 p1 := by apply List.prefix_of_prefix_length_le g2 g1; linarith
  have :  byteSize p2 < byteSize p1 :=by apply prefix_byteSize_lt this ; assumption
  simp only [byteSize] at this
  linarith

lemma byteSize_le_of_length_le (g1: List.IsPrefix p1 s) (g2: List.IsPrefix p2 s)
   (gi: p1.length ≤ p2.length) : byteSize p1 ≤ byteSize p2 :=by
  have g:= List.prefix_of_prefix_length_le g1 g2 gi
  apply prefix_byteSize_le g

lemma prefix_of_byteSize_le (g1: List.IsPrefix p1 s) (g2: List.IsPrefix p2 s)
   (gi: byteSize p1 ≤ byteSize p2) : List.IsPrefix p1 p2 :=by
  have g:= length_le_of_byteSize_le g1 g2 gi
  apply List.prefix_of_prefix_length_le g1 g2 g

lemma byteSize_le_iif_length_le (g1: List.IsPrefix p1 s) (g2: List.IsPrefix p2 s)
    : byteSize p1 ≤ byteSize p2 ↔  p1.length ≤ p2.length:=by
  constructor; intro gi; apply length_le_of_byteSize_le g1 g2 gi
  intro gi; apply byteSize_le_of_length_le g1 g2 gi


/-
Function: is_char_boundary
From: core::str::is_char_boundary
Description: https://doc.rust-lang.org/std/primitive.str.html#method.is_char_boundary
-/

@[simp]
def is_char_boundary (s: Str) (i: Nat) := match s with
  | [] => i == 0
  | h::t => if i = 0 then true else
      if i < Char.utf8Size h then false else is_char_boundary t (i - Char.utf8Size h)

def is_char_boundary_def (s: Str) (i: Nat) := i ∈ ListCharPos s ∨  i = byteSize s

theorem is_char_boundary_EQ : is_char_boundary s i =  is_char_boundary_def s i := by
  induction s generalizing i
  unfold is_char_boundary is_char_boundary_def ListCharPos ListCharPos_aux byteSize
  simp only [beq_iff_eq, not_mem_nil, false_or]
  rename_i h t ind
  unfold is_char_boundary is_char_boundary_def
  have : ∀ m l, m ∈ ListCharPos l ∨ m = byteSize l ↔ m ∈ (ListCharPos l ++ [byteSize l]) :=by
    intro m l; simp only [ListCharPos,byteSize, mem_append, mem_singleton]
  rw[this, ← CharBoundPos_def,  ← CharBoundPos_EQ]
  unfold CharBoundPos CharBoundPos_aux
  split; rename_i g; simp only [g, zero_add, mem_cons, true_or]
  split; rename_i g _; simp only [zero_add, mem_cons, g, not_false_eq_true, not_sym, false_or, eq_iff_iff, false_iff]
  rw[CharBoundPos_aux_para1_elim]; by_contra; rename_i gi
  simp only [CharBoundPos, mem_map] at gi; obtain⟨a, ga⟩ := gi; omega
  rename_i gi1 gi2; simp only [zero_add, mem_cons, gi1, not_false_eq_true, not_sym, false_or, eq_iff_iff]
  rw[CharBoundPos_aux_para1_elim]; simp only [CharBoundPos, mem_map]
  constructor; intro g; rw[ind, is_char_boundary_def, this, ← CharBoundPos_def, ← CharBoundPos_EQ, CharBoundPos] at g;
  use i - Char.utf8Size h; simp only [g, true_and]; omega
  intro g; obtain⟨a, ga⟩ := g ; rw[ind, is_char_boundary_def, this, ← CharBoundPos_def,  ← CharBoundPos_EQ, CharBoundPos]
  have :  i - Char.utf8Size h = a := by omega
  rw[this]; simp only [ga]


lemma byteSize_prefix_is_char_boundary: List.IsPrefix p s  →  is_char_boundary s (byteSize p) := by
  induction s generalizing p
  simp only [prefix_nil, is_char_boundary, if_false_right, and_true]
  intro g; rw[g]; simp only [byteSize, beq_self_eq_true]
  rename_i h t ind ;
  intro g; unfold is_char_boundary
  cases p ; simp only [byteSize, ↓reduceIte]
  rename_i hp tp; have g:=prefix_cons g; rw[g.left];
  simp only [byteSize, add_eq_zero, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte, add_tsub_cancel_left, if_true_left]
  simp only [ind g.right, ite_self]


lemma is_char_boundary_zero : is_char_boundary s 0 :=by
  unfold is_char_boundary; simp only [beq_self_eq_true, ↓reduceIte]
  split; simp only; simp only



/-
Function: function: char_indices
From: core::str::char_indices
Description: https://doc.rust-lang.org/std/primitive.str.html#method.char_indices
-/

def char_indices_def (s : Str) : List (Nat × Char):= zip (ListCharPos s) s

@[simp]
def char_indices_def_aux (s: Str) (i: Nat) := zip (ListCharPos_aux s i) s

@[simp]
def char_indices_aux (s : Str) (i : Nat): List (Nat × Char) := match s with
  | [] => []
  | h::t => (i, h) :: char_indices_aux t (i + Char.utf8Size h)

@[simp]
def char_indices s := char_indices_aux s 0

lemma char_indices_aux_EQ : char_indices_def_aux s i = char_indices_aux s i :=by
  induction s generalizing i
  simp only [char_indices_def_aux, ListCharPos_aux, zip_nil_right, char_indices_aux] ;
  rename_i h t ind
  generalize lhs: char_indices_def_aux (h :: t) i = l
  generalize rhs: char_indices_aux (h :: t) i = r
  simp only [char_indices_aux] at rhs;
  have : l = (i,h) :: char_indices_def_aux t (i + Char.utf8Size h) := by
    simp only [char_indices_def_aux, ListCharPos_aux] at lhs; split at lhs;
    simp_all only [char_indices_def_aux, ListCharPos_aux, zip_nil_right, char_indices_aux, forall_const,
      zip_cons_cons]
    simp only [zip_cons_cons] at lhs;
    simp_all only [char_indices_def_aux, ListCharPos_aux, char_indices_aux]
  simp_all only [char_indices_def_aux, ListCharPos_aux]


lemma char_indices_EQ : char_indices s = char_indices_def s := by
  unfold char_indices; rw [← char_indices_aux_EQ]; unfold char_indices_def char_indices_def_aux ListCharPos;
  simp only


/-
Function: split_at
From: core::str::split_at
Description: https://doc.rust-lang.org/std/primitive.str.html#method.split_at
-/

def split_at_aux (s: Str) (i: Nat) (ks: Str): Option (List Char × List Char)  := match s with
  | [] => if i = 0 then some (ks, []) else none
  | h::t => if i = 0 then some (ks, h::t) else if i < Char.utf8Size h then none
            else split_at_aux t (i - Char.utf8Size h) (ks++[h])

def split_at (s: Str) (i: Nat) := split_at_aux s i []

lemma split_at_aux_para1_elim: split_at_aux s i ks = some (s1, s2) ↔  ∃ t1, s1 = ks ++ t1 ∧  split_at s i = some (t1, s2) :=by
  induction s generalizing i ks s1 s2
  unfold split_at split_at_aux; split; rename_i gi; simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
  constructor
  intro g1 ; use []; simp only [g1, and_self, and_true]; rw[← g1.right]; simp only [List.append_nil]
  intro g; obtain ⟨t1, g⟩:=g ; rw[g.left, ← g.right.left, ← g.right.right]; simp only [List.append_nil,and_self]
  simp only [and_false, exists_const, IsEmpty.forall_iff]
  rename_i h t ind ;
  constructor; intro g
  unfold split_at_aux at g; split at g; simp only [Option.some.injEq, Prod.mk.injEq] at g
  use []; rename_i gi; rw[gi, g.left]; unfold split_at split_at_aux
  simp only [List.append_nil, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]; exact g.right
  split at g; contradiction; have g:= ind.mp g ; obtain ⟨t1, g⟩:=g
  use [h]++ t1; simp only [g, List.append_assoc, singleton_append, true_and]
  unfold split_at split_at_aux;  split; omega; simp only [List.nil_append]
  apply (@ind (i - Char.utf8Size h) [h] (h::t1) s2).mpr
  use t1; simp only [singleton_append, g, and_self]
  intro g; obtain ⟨t1,g⟩ := g
  unfold split_at_aux; split; simp only [Option.some.injEq, Prod.mk.injEq]
  rename_i gi; rw[gi] at g; unfold split_at split_at_aux at g
  simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at g
  simp only [g, and_true]; rw[← g.right.left]; simp only [List.append_nil]
  split; unfold split_at split_at_aux at g; split at g; omega; simp only [and_false] at g
  apply (@ind (i - Char.utf8Size h) (ks++[h]) s1 s2).mpr
  unfold split_at split_at_aux at g; split at g; omega; simp only [List.nil_append] at g
  have g1:= ind.mp g.right; obtain ⟨tx, g1⟩:=g1
  use tx; simp only [g, g1, singleton_append, List.append_assoc, and_self]

lemma split_at_aux_none : split_at_aux s i ks = none ↔ split_at s i = none :=by
  constructor;
  intro g; generalize gi: split_at s i = sp
  cases sp; simp only; rename_i v
  have : ∃ t1, ks ++ v.1 = ks ++ t1 ∧  split_at s i = some (t1, v.2) := by use v.1
  have := split_at_aux_para1_elim.mpr this;
  simp only [this, not_false_eq_true, not_sym] at g
  intro g; generalize gi: split_at_aux s i ks = sp
  cases sp; simp only;
  have gi := split_at_aux_para1_elim.mp gi; obtain ⟨x, gi⟩:=gi
  simp only [g, not_false_eq_true, not_sym, and_false] at gi

lemma split_at_aux_none_sound : split_at_aux s i ks = none ↔ ¬ ∃ s1, List.IsPrefix s1 s ∧ byteSize s1 = i :=by
  induction s generalizing i ks
  unfold split_at_aux;
  simp only [ite_eq_right_iff, not_false_eq_true, not_sym, imp_false, prefix_nil, exists_eq_left]
  simp only [byteSize, byteSize_aux]; omega
  rename_i h t ind
  unfold split_at_aux;
  constructor; intro g ; split at g; contradiction; split at g;
  by_contra; rename_i g1; obtain ⟨s1, g1⟩ := g1
  cases s1; simp only [_root_.nil_prefix, byteSize, byteSize_aux, true_and] at g1; omega
  rename_i hs1 ts1; simp only [byteSize_cons] at g1
  have g2:= prefix_cons g1.left ; rw[g2.left] at g1 ; omega
  have g:= ind.mp g; by_contra; rename_i g1; obtain ⟨s1, g1⟩ := g1
  cases s1; simp only [_root_.nil_prefix, byteSize, byteSize_aux, true_and] at g1; omega
  rename_i hs1 ts1; simp only [byteSize_cons] at g1
  have g2:= prefix_cons g1.left ; rw[g2.left] at g1 ;
  simp only [not_exists, not_and] at g; have g:=g ts1 g2.right; omega
  --mpr
  simp only [not_exists, not_and]; intro g
  split; have g:= g []; simp only [_root_.nil_prefix, byteSize, byteSize_aux, forall_true_left] at g; omega
  split; simp only; apply ind.mpr
  by_contra; rename_i g1; obtain ⟨s1, g1⟩ := g1
  have : List.IsPrefix (h :: s1) (h :: t) :=by apply prefix_cons_mpr g1.left
  have g:= g (h::s1) this; simp only [byteSize_cons] at g; omega

theorem split_at_none_sound : split_at s i = none ↔ ¬ ∃ s1, List.IsPrefix s1 s ∧ byteSize s1 = i :=by
  unfold split_at; exact split_at_aux_none_sound


theorem split_at_some_sound : split_at s i= some (s1, s2) ↔ byteSize s1 = i ∧ s = s1 ++ s2 :=by
  induction s generalizing i s1 s2
  unfold split_at split_at_aux ; split
  constructor; simp only [Option.some.injEq, Prod.mk.injEq, nil_eq_append, and_imp]
  intro g1 g2; rename_i gi; rw[← g1, gi]; simp only [g2, and_self, and_true]; rw[byteSize_aux_para1_elim]
  rw[← g2]; simp only [byteSize_aux]
  simp only [nil_eq_append, Option.some.injEq, Prod.mk.injEq, and_imp]
  intro _ g2 g3; rw[g2,g3]; simp only [and_self]
  constructor; simp only [nil_eq_append, IsEmpty.forall_iff]
  simp only [nil_eq_append, and_imp, imp_false]; intro g1 g2
  rw[g2] at g1; simp only [byteSize, byteSize_aux] at g1; omega
  rename_i h t ind
  constructor
  intro g; unfold split_at split_at_aux at g
  split at g; simp only [Option.some.injEq, Prod.mk.injEq] at g; rename_i gi
  rw[gi, ← g.left]; simp only [byteSize, byteSize_aux, g.right, List.nil_append, and_self]
  split at g; contradiction; simp only [List.nil_append] at g
  have g:= split_at_aux_para1_elim.mp g; obtain ⟨t1, g⟩ := g
  have g1:= ind.mp g.right
  simp only [g, singleton_append, byteSize_cons, g1, cons_append, and_true];
  simp only [List.nil_append, and_true]; omega
  --mpr
  intro g ; unfold split_at split_at_aux; split ; rename_i gi
  rw[gi] at g; have gs1:= nil_of_byteSize_zero g.left ; rw[g.right, gs1]; simp only [List.nil_append]
  split; cases s1; simp only [byteSize, byteSize_aux, List.nil_append] at g; omega
  rename_i hs1 ts1; simp only [byteSize_cons, cons_append, cons.injEq] at g;
  rename_i gi; rw [g.right.left] at gi; omega
  simp only [List.nil_append]; rw[split_at_aux_para1_elim]
  cases s1; simp only [byteSize, byteSize_aux, List.nil_append] at g; omega
  rename_i hs1 ts1; simp only [byteSize_cons, cons_append, cons.injEq] at g;
  use ts1; simp only [g, singleton_append, true_and]; rw[← g.right.right]
  apply ind.mpr; constructor; omega; exact g.right.right


lemma split_at_zero: split_at s 0 = some ([], s) := by
  unfold split_at split_at_aux; simp only [↓reduceIte]
  split; simp only; simp only

lemma split_at_none_of_not_char_boundary: ¬ is_char_boundary s i ↔  split_at s i = none :=by
  induction s generalizing i
  unfold is_char_boundary split_at split_at_aux
  simp only [beq_iff_eq, ite_eq_right_iff, not_false_eq_true, not_sym, imp_false]
  rename_i h t ind
  unfold is_char_boundary split_at split_at_aux
  constructor
  intro g; split at g; contradiction; split at g
  rename_i g0 g1; simp only [g0, not_false_eq_true, not_sym, ↓reduceIte, g1]
  rename_i g0 g1; simp only [g0, not_false_eq_true, not_sym, ↓reduceIte, g1, List.nil_append]
  have ind:= ind.mp g; exact split_at_aux_none.mpr ind
  simp only [List.nil_append, ite_eq_left_iff, Bool.ite_eq_true_distrib, not_false_eq_true, not_sym,
    if_false_left, not_lt, not_forall, not_and, Bool.not_eq_true, exists_prop]
  split; simp only [IsEmpty.forall_iff];
  split; simp_all only [Bool.not_eq_true, not_false_eq_true, not_sym, isEmpty_Prop, not_le,
    IsEmpty.forall_iff, and_self, forall_true_left]
  simp_all only [Bool.not_eq_true, not_lt, not_false_eq_true, not_sym, forall_true_left, true_and]
  exact split_at_aux_none.mp




--#eval ListCharPos "L∃∀N".data
--#eval split_at "La∃∀N".data 5


/-
Function: string_slice
From: core::str::get
Description: https://doc.rust-lang.org/std/primitive.str.html#method.get
-/

def string_slice (s: Str) (p1 p2: Nat):= if p2 < p1 then none else do let (_,s2) ← split_at s p1
                                                                      let (s21, _) ← (split_at s2 (p2-p1))
                                                                      some s21

--#eval ListCharPos "La∃∀N".data
--#eval string_slice "La∃∀N".data  5 1

/-
For special cases: get(0..a)
Function: PrefixFromPos
From: core::str::get
Description: https://doc.rust-lang.org/std/primitive.str.html#method.get
-/

def PrefixFromPos_safe_r (s: Str) (i: Nat): Str := match s with
  | [] => []
  | h::t => if i = 0 then [] else h::PrefixFromPos_safe_r t (i - Char.utf8Size h)

@[simp]
def PrefixFromPos (s: Str) (i: Nat): Option Str :=
      if is_char_boundary s i then some (PrefixFromPos_safe_r s i) else none

lemma PrefixFromPos_none_sound: PrefixFromPos s i = none ↔ ¬ is_char_boundary s i :=by
  unfold PrefixFromPos
  split; rename_i g; simp only [g, not_true_eq_false]
  rename_i g; simp only [g, Bool.false_eq_true, not_false_eq_true, not_sym]

lemma PrefixFromPos_some_sound: PrefixFromPos s i = some p ↔ (List.IsPrefix p s) ∧ (byteSize p = i) := by
  unfold PrefixFromPos ;
  split; simp only [Option.some.injEq, byteSize]
  induction s generalizing i p
  rename_i h;
  simp only [is_char_boundary, beq_iff_eq] at h;
  rw[h]; unfold PrefixFromPos_safe_r;
  constructor
  intro h0; rw[← h0]; simp only [self_prefix, byteSize, and_self]
  intro h0; simp only [prefix_nil] at h0; symm; exact h0.left
  rename_i head tail ind h
  unfold PrefixFromPos_safe_r
  constructor;
  intro ih
  cases p ; simp only [ite_eq_left_iff, not_false_eq_true, not_sym, imp_false, not_not] at ih ;
  simp only [List.nil_prefix, byteSize, ih, and_self]
  rename_i hl tl; split at ih; contradiction
  have ih := List.cons_eq_cons.mp ih
  rw[ih.left];
  simp only [is_char_boundary, ite_eq_left_iff, Bool.ite_eq_true_distrib, not_false_eq_true,
    not_sym, if_false_left, not_lt] at h;
  rename_i hp _; simp only [hp, not_false_eq_true, not_sym, forall_true_left] at h
  have ind:= (ind h.right).mp ih.right
  constructor; apply prefix_cons_mpr ind.left hl;
  simp only [byteSize] ; rw[← ih.left]; omega
  cases p; simp only [_root_.nil_prefix, byteSize_aux, true_and, ite_eq_left_iff, not_false_eq_true,
    not_sym, imp_false, not_not]
  intro hp; symm at hp; exact hp
  rename_i hl tl; intro h1;
  have ih := prefix_cons h1.left
  split; rename_i hp; simp only [byteSize, zero_add, hp] at h1
  have i2 : Char.utf8Size hl >0 := by apply Char.utf8Size_pos
  omega
  rw [ih.left];
  simp only [is_char_boundary, ite_eq_left_iff, Bool.ite_eq_true_distrib, not_false_eq_true,
    not_sym, if_false_left, not_lt] at h
  rename_i hp; simp only [hp, not_false_eq_true, not_sym, forall_true_left] at h
  simp only [byteSize, zero_add] at h1;
  simp only [cons.injEq, true_and]
  have v1 : byteSize tl  = i - Char.utf8Size hl := by omega
  have v: (tl <+: tail) ∧ byteSize tl  = i - Char.utf8Size hl := by
    apply And.intro ih.right v1
  rw[ih.left] at v
  have ind:= (ind h.right).mpr v
  rw[ind]; constructor; simp only [byteSize, IsEmpty.forall_iff]
  rename_i h; simp at h
  intro h0
  have h0r := h0.right; symm at h0r
  have h1 := byteSize_prefix_is_char_boundary h0.left; rw[h0.right] at h1
  rw[h1] at h; contradiction

lemma PrefixFromPos_byteSize : PrefixFromPos s i = some p →  byteSize p = i := by
  intro h ;
  have h1 := PrefixFromPos_some_sound.mp h
  exact h1.right

lemma is_char_boundary_from_prefix (h: PrefixFromPos s i = some pre)
    : is_char_boundary s i := by
  unfold PrefixFromPos at h
  split at h; assumption; contradiction

lemma PrefixFromPos_self: PrefixFromPos s0 (byteSize s0) = some s0 :=by
  apply PrefixFromPos_some_sound.mpr; simp

lemma PrefixFromPos_prefix (hp: List.IsPrefix i s) : PrefixFromPos s (byteSize i) = some i := by
  apply PrefixFromPos_some_sound.mpr; simp [hp]

lemma PrefixFromPos_eq_split_at_none: PrefixFromPos s i = none ↔  split_at s i = none :=by
  simp only [PrefixFromPos, ite_eq_right_iff, not_false_eq_true, not_sym, imp_false,
    Bool.not_eq_true]
  rw [← split_at_none_of_not_char_boundary]; simp only [Bool.not_eq_true]

lemma PrefixFromPos_eq_split_at_aux_some: PrefixFromPos s i = some u ↔ ∃ v, split_at s i= some (u,v) :=by
  induction s generalizing i  u
  unfold PrefixFromPos split_at split_at_aux is_char_boundary
  simp only [beq_iff_eq, ite_some_none_eq_some, Prod.mk.injEq, exists_and_left, exists_eq',
    and_true, and_congr_right_iff]
  intro g; rw[g,PrefixFromPos_safe_r]
  rename_i h t ind
  unfold PrefixFromPos split_at split_at_aux is_char_boundary
  split; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq, exists_and_left, exists_eq', and_true]
  rename_i g; rw[g]; unfold PrefixFromPos_safe_r; simp only [↓reduceIte]
  split; simp only [↓reduceIte, not_false_eq_true, not_sym, exists_const]
  split; rename_i g0 g1 g2;
  simp only [PrefixFromPos_safe_r, g0, not_false_eq_true, not_sym, ↓reduceIte, Option.some.injEq, List.nil_append]
  cases u; simp only [not_false_eq_true, not_sym, false_iff, not_exists]
  by_contra; rename_i gc; simp only [not_forall, not_not] at gc; obtain⟨x, gc⟩:=gc
  have gc:= split_at_aux_para1_elim.mp gc ;
  simp only [singleton_append, not_false_eq_true, not_sym, false_and, exists_const] at gc
  rename_i hu tu; simp only [cons.injEq]
  have ind:= @ind (i - Char.utf8Size h) tu
  simp only [PrefixFromPos, g2, ↓reduceIte, Option.some.injEq, List.append_assoc,
    singleton_append] at ind
  constructor; intro g;
  have ind:= ind.mp g.right; obtain ⟨v, gv⟩:= ind
  have k:= (@split_at_aux_para1_elim t (i - Char.utf8Size h) [hu] ([hu]++tu) v).mpr (by use tu)
  simp only [singleton_append] at k; rw[g.left]; rw[g.left] at k; use v
  intro g; obtain ⟨v, gv⟩:= g; have gv:= split_at_aux_para1_elim.mp gv; obtain ⟨x, gv⟩:= gv
  simp only [singleton_append, cons.injEq] at gv; rw[← gv.left.right] at gv
  have ind:=ind.mpr (by use v; exact gv.right)
  simp only [gv.left.left, ind, and_self]
  rename_i g; have g:= split_at_none_of_not_char_boundary.mp g
  have g: split_at_aux t (i - Char.utf8Size h) [h] = none := by apply split_at_aux_none.mpr g
  simp only [List.nil_append, g, not_false_eq_true, not_sym, exists_const]

lemma PrefixFromPos_eq_string_slice : PrefixFromPos s i = string_slice s 0 i :=by
  simp only [ string_slice, not_lt_zero', ↓reduceIte, tsub_zero, Option.bind_eq_bind]
  generalize gi: PrefixFromPos s i = osp
  cases osp ; have gi1:= gi;  unfold PrefixFromPos at gi ; split at gi ; contradiction
  unfold Option.bind; rw[split_at_zero]; simp only
  rw[PrefixFromPos_eq_split_at_none.mp gi1]
  rw[split_at_zero]; simp only [Option.some_bind]
  rename_i v; have g:= PrefixFromPos_eq_split_at_aux_some.mp gi; obtain ⟨x,g⟩:=g
  simp only [g, Option.some_bind]



/-
Function: floor_char_boundary
From: str::core::floor_char_boundary
Description: https://doc.rust-lang.org/std/primitive.str.html#method.floor_char_boundary
-/

def floor_char_boundary_aux (s: Str) (i: Nat) (k: Nat): Nat := match s with
  | [] => k
  | h::t => if i < Char.utf8Size h then k else floor_char_boundary_aux t (i - Char.utf8Size h) (k + Char.utf8Size h)

def floor_char_boundary (s: Str) (i: Nat) := floor_char_boundary_aux s i 0

lemma floor_char_boundary_aux_ge: floor_char_boundary_aux s i k  ≥ k := by
  induction s generalizing i k
  unfold floor_char_boundary_aux; simp only [ge_iff_le, le_refl]
  rename_i h t ind
  unfold floor_char_boundary_aux; split; simp only [ge_iff_le, le_refl]
  have ind:= @ind (i - h.utf8Size) (k + h.utf8Size) ; linarith

lemma floor_char_boundary_aux_para1_elim: floor_char_boundary_aux s i k = k + floor_char_boundary s i := by
  unfold floor_char_boundary
  induction s generalizing i k
  unfold floor_char_boundary_aux; simp only [add_zero]
  rename_i h t ind
  unfold floor_char_boundary_aux; split; simp only [add_zero]
  rw[ind]; simp only [zero_add];
  have : floor_char_boundary_aux t (i - Char.utf8Size h) (Char.utf8Size h) =
        Char.utf8Size h + floor_char_boundary_aux t (i - Char.utf8Size h) 0 := by apply ind
  rw[this]; linarith

def is_floor_char_boundary (s: Str) (i: Nat) (fcb: Nat) := ((is_char_boundary s fcb) ∧ (fcb ≤ i)) ∧ (∀ j, ((is_char_boundary s j) ∧ (j ≤ i)) → j ≤ fcb )

theorem floor_char_boundary_sound:  floor_char_boundary s i = fcb ↔ is_floor_char_boundary s i fcb :=by
  apply Eq_iff_of_unique_and_mp unique_maxima ; intro fcb
  induction s generalizing i fcb
  unfold floor_char_boundary floor_char_boundary_aux is_char_boundary at *
  intro g; rw[← g];
  simp only [beq_self_eq_true, _root_.zero_le, and_self, beq_iff_eq, nonpos_iff_eq_zero, and_imp, forall_eq, imp_self]
  rename_i h t ind
  unfold is_char_boundary floor_char_boundary floor_char_boundary_aux
  intro g
  split at g; rw[← g];
  simp only [↓reduceIte, _root_.zero_le, and_self, Bool.if_false_left,
    Bool.if_true_left, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt, nonpos_iff_eq_zero, and_imp, forall_eq_or_imp, imp_self, true_and]
  intro a g1 _ g3; omega
  split; rename_i g;
  have gj2: Char.utf8Size h > 0 :=by apply Char.utf8Size_pos
  rename_i gf ; symm at gf; have gj:= @floor_char_boundary_aux_ge t (i - h.utf8Size) (0 + h.utf8Size); omega
  simp only [Bool.if_false_left, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    not_lt, Bool.if_true_left, Bool.or_eq_true, decide_eq_true_eq, and_imp, forall_eq_or_imp,
    _root_.zero_le, imp_self, true_and]
  simp only [zero_add, floor_char_boundary_aux_para1_elim] at g;
  have g: fcb - Char.utf8Size h = floor_char_boundary t (i - Char.utf8Size h) :=by omega
  symm at g
  have ind:= ind (fcb - h.utf8Size) g; simp only [ind, and_true]
  constructor; omega; intro p0 g1 g2 g3;
  have ind := ind.right (p0 - h.utf8Size) ⟨g2, (by omega)⟩
  omega


/-
#eval ListCharPos "L∃∀N".data
#eval floor_char_boundary "L∃∀N".data 15
-/

/-
Function: ceiling_char_boundary
From: str::core::ceiling_char_boundary
Description: https://doc.rust-lang.org/std/primitive.str.html#method.ceiling_char_boundary
-/


def ceiling_char_boundary_aux (s: Str) (i: Nat) (k: Nat): Nat := match s with
  | [] => k
  | h::t =>
      if i = 0 then k else
      if i < Char.utf8Size h then k + Char.utf8Size h else ceiling_char_boundary_aux t (i - Char.utf8Size h) (k + Char.utf8Size h)

def ceiling_char_boundary (s: Str) (i: Nat) := ceiling_char_boundary_aux s i 0


lemma ceiling_char_boundary_aux_ge: ceiling_char_boundary_aux s i k  ≥ k := by
  induction s generalizing i k
  unfold ceiling_char_boundary_aux; simp only [ge_iff_le, le_refl]
  rename_i h t ind
  unfold ceiling_char_boundary_aux; split; simp only [ge_iff_le, le_refl]
  split; simp only [ge_iff_le, le_add_iff_nonneg_right, _root_.zero_le]
  have ind:= @ind (i - h.utf8Size) (k + h.utf8Size) ; linarith

lemma ceiling_char_boundary_aux_para1_elim: ceiling_char_boundary_aux s i k = k + ceiling_char_boundary s i := by
  unfold ceiling_char_boundary
  induction s generalizing i k
  unfold ceiling_char_boundary_aux; simp only [add_zero]
  rename_i h t ind
  unfold ceiling_char_boundary_aux; split; simp only [add_zero]
  rw[ind]; simp only [zero_add]; split; simp only
  have : ceiling_char_boundary_aux t (i - Char.utf8Size h) (Char.utf8Size h) = Char.utf8Size h + ceiling_char_boundary_aux t (i - Char.utf8Size h) 0 := by apply ind
  rw[this]; linarith


-- based on the behavior of the Rust ceiling_char_boundary function:
theorem ceiling_char_boundary_sound_sp_case (gis: i > byteSize s) : ceiling_char_boundary s i = byteSize s := by
  induction s generalizing i;
  simp only [ceiling_char_boundary, ceiling_char_boundary_aux, byteSize, byteSize_aux]
  rename_i h t ind
  rw[byteSize_cons] at *; simp only [ceiling_char_boundary, ceiling_char_boundary_aux]
  have i1: ¬ i = 0 := by omega
  have i2: ¬ i < Char.utf8Size h := by omega
  simp only [i1, not_false_eq_true, not_sym, ↓reduceIte, i2, zero_add, ceiling_char_boundary_aux_para1_elim]
  have i1: i - Char.utf8Size h > byteSize t := by omega
  have ind:=ind i1; rw[ind]

def is_ceiling_char_boundary (s: Str) (i: Nat) (ccb: Nat):= ((is_char_boundary s ccb) ∧ (ccb ≥  i)) ∧ (∀ j, ((is_char_boundary s j) ∧ (j ≥  i)) → j ≥ ccb )

theorem ceiling_char_boundary_sound (gis: i ≤ byteSize s): ceiling_char_boundary s i = ccb
          ↔ is_ceiling_char_boundary s i ccb :=by
  apply Eq_iff_of_unique_and_mp unique_minima ; intro ccb
  induction s generalizing i ccb
  simp only [byteSize, byteSize_aux, nonpos_iff_eq_zero] at gis; rw[gis]
  unfold ceiling_char_boundary ceiling_char_boundary_aux is_char_boundary
  intro g; rw[← g]
  simp only [beq_self_eq_true, ge_iff_le, le_refl, and_self, beq_iff_eq, _root_.zero_le, and_true, implies_true]
  rename_i h t ind
  unfold ceiling_char_boundary ceiling_char_boundary_aux is_char_boundary
  intro g; split at g; rw[← g]; rename_i gi; rw[gi]
  simp only [↓reduceIte, ge_iff_le, le_refl, and_self, Bool.if_false_left, Bool.if_true_left,
    Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt, _root_.zero_le, and_true, implies_true]
  have i1: Char.utf8Size h > 0 := by apply Char.utf8Size_pos
  split at g; simp only [zero_add] at g
  rw[← g]; rename_i gi;
  simp only [lt_self_iff_false, ↓reduceIte, le_refl, tsub_eq_zero_of_le, is_char_boundary_zero,
    ite_self, ge_iff_le, true_and, Bool.if_false_left, Bool.if_true_left, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
    and_imp, forall_eq_or_imp, nonpos_iff_eq_zero]
  constructor; omega; constructor; intro _; contradiction
  intro a g1 _ _ ; exact g1
  have := @ceiling_char_boundary_aux_ge t (i - h.utf8Size) (0 + h.utf8Size);
  split; omega; split; omega
  simp only [zero_add, ceiling_char_boundary_aux_para1_elim] at g;
  have g: ccb - Char.utf8Size h = ceiling_char_boundary t (i - Char.utf8Size h) :=by omega
  simp only [byteSize] at gis; symm at g
  have id1: (i - h.utf8Size) ≤  byteSize t := by omega
  have ind:= ind id1 (ccb - h.utf8Size) g
  constructor
  simp only [ind, ge_iff_le, true_and]; omega
  intro p0; split; intro _; omega
  split; simp only [ge_iff_le, false_and, false_implies]
  intro gp0; have gp0:= ind.right (p0 - h.utf8Size) ⟨gp0.left, (by omega)⟩
  omega


--#eval ListCharPos "L∃∀N".data
--#eval ceiling_char_boundary "L∃∀N".data 2


--#eval split_at "abcdef".data 7

/-
Rust Pattern type
-/

inductive Pattern: Type
  | SingleChar (c: Char)
  | ListChar (l: Str)
  | FilterFunction (f: Char → Bool)
  | WholeString (s: Str)


/-
Function: contains
From: str::core::contains
Description: https://doc.rust-lang.org/std/primitive.str.html#method.contains
-/


def contains_substring_def (s: Str) (ss: Str) := ∃ s1 s2, s = s1 ++ ss ++ s2

def contains_substring (s: Str) (ss: Str)  := match s, ss with
  | _ , [] => true
  | [], _ => false
  | _::ts, _ => if List.isPrefixOf ss s then true else contains_substring ts ss

theorem contains_substring_EQ : contains_substring s ss  = contains_substring_def s ss :=by
  induction s generalizing ss
  cases ss
  simp only [contains_substring, contains_substring_def, List.append_nil, nil_eq_append, exists_eq_right, exists_eq]
  simp only [contains_substring, not_false_eq_true, not_sym, contains_substring_def, List.append_assoc,
    cons_append, nil_eq_append, and_false, exists_const]
  rename_i h t ind
  by_cases (ss = []) ; rename_i gs; rw[gs]
  simp only [contains_substring, contains_substring_def, List.append_nil, eq_iff_iff, true_iff]
  use [h], t; simp only [singleton_append]
  simp only [contains_substring, ite_eq_left_iff, Bool.not_eq_true, contains_substring_def, List.append_assoc,
    cons_append, eq_iff_iff]
  by_cases (List.isPrefixOf ss (h :: t) = true)
  rename_i gs1; have gs1:= IsPrefix_isPrefixOf_EQ.mp gs1; unfold List.IsPrefix at gs1; obtain ⟨t1, gt1⟩:=gs1
  have: ∃ s1 s2, h :: t = s1 ++ (ss ++ s2) :=by use [], t1; simp only [gt1, List.nil_append]
  simp only [gs1, not_false_eq_true, not_sym, IsEmpty.forall_iff, this]
  rename_i gs1; simp only [gs1, forall_true_left]; rw[ind]; unfold contains_substring_def
  constructor;
  intro gt; obtain ⟨s1, s2, gt⟩ := gt
  use h::s1, s2; simp only [gt, List.append_assoc, cons_append]
  intro gt; obtain ⟨s1, s2, gt⟩ := gt
  cases s1; cases ss; cases s2; simp only [List.append_nil, not_false_eq_true, not_sym] at gt
  simp only [List.nil_append, cons.injEq] at gt; rename_i t1
  use t1, []; simp only [gt, List.append_nil]
  rename_i hp tp _; simp only [List.nil_append] at gt
  rw[IsPrefix_isPrefixOf_EQ] at gs1; unfold List.IsPrefix at gs1; symm at gt
  have : ∃ t_1, hp :: tp ++ t_1 = h :: t :=by use s2;
  contradiction; rename_i hp tp; simp only [cons_append, cons.injEq] at gt
  use tp,s2; simp only [gt, List.append_assoc]


def contains_char_filter_def  (s: Str) (f: Char → Bool) := ∃ c ∈ s, f c

def contains_char_filter  (s: Str) (f: Char → Bool) := match s with
  | [] => false
  | h::t => if f h then true else contains_char_filter t f

theorem contains_char_filter_EQ : contains_char_filter s f  = contains_char_filter_def s f :=by
  induction s;
  unfold contains_char_filter contains_char_filter_def
  simp only [not_false_eq_true, not_sym, not_mem_nil, false_and, exists_const]
  rename_i h t ind ;
  unfold contains_char_filter contains_char_filter_def
  split; rename_i g1; simp only [mem_cons, exists_eq_or_imp, g1, true_or]
  rename_i gh; simp only [ind, contains_char_filter_def, mem_cons, exists_eq_or_imp, gh,
    not_false_eq_true, not_sym, false_or]


----#eval contains_substring "aaabcfeff".data "a".data

def contains (s: Str) (P: Pattern) : Bool := match P with
  | Pattern.SingleChar c => contains_char_filter s (fun x => x = c)
  | Pattern.ListChar l => contains_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => contains_char_filter s f
  | Pattern.WholeString ss => contains_substring s ss

lemma contains_substring_of_isPrefixOf: List.isPrefixOf ss s → contains_substring s ss :=by
  intro g; have g:= IsPrefix_isPrefixOf_EQ.mp g ; unfold List.IsPrefix at g; obtain ⟨u,g⟩:= g
  rw[contains_substring_EQ]; unfold contains_substring_def; use [], u; simp only [List.nil_append,g]

lemma contains_substring_of_isSuffixOf: List.isSuffixOf ss s → contains_substring s ss :=by
  intro g; have g:= IsSuffix_isSuffixOf_EQ.mp g ; unfold List.IsPrefix at g; obtain ⟨u,g⟩:= g
  rw[contains_substring_EQ]; unfold contains_substring_def; use u, []; simp only [g, append_nil]

lemma contains_substring_cons: contains_substring t ss → contains_substring (h::t) ss :=by
  intro g; cases ss
  . simp only [contains_substring]
  . simp only [contains_substring, g, ite_self]

lemma contains_substring_cons_cons : contains_substring (hs :: ts) (hu::tu) = true  → contains_substring ts tu = true :=by
  intro g; simp only [contains_substring, Bool.if_true_left, Bool.decide_eq_true,Bool.or_eq_true] at g
  cases g;
  . rename_i g; simp only [isPrefixOf, Bool.and_eq_true, beq_iff_eq] at g;
    exact contains_substring_of_isPrefixOf g.right
  . rename_i g; rw[contains_substring_EQ, contains_substring_def] at g; obtain ⟨s1,s2,g⟩:= g
    rw[contains_substring_EQ, contains_substring_def]
    use s1++[hu], s2; rw[g]; simp only [append_assoc, cons_append, singleton_append]
    simp only [nil_append]

lemma contains_substring_substring_cons: contains_substring s (h::t) → contains_substring s t :=by
  simp only [contains_substring_EQ, contains_substring_def]
  intro g; obtain⟨s1,s2,g⟩:=g
  use s1++[h], s2; simp only [g, append_assoc, cons_append, singleton_append]; simp only [nil_append]

lemma contains_substring_trans: contains_substring s s1 → contains_substring s1 s2 → contains_substring s s2 :=by
  intro g1 g2
  rw[contains_substring_EQ, contains_substring_def] at *
  obtain⟨u1, u2, g1⟩:= g1; obtain⟨v1, v2, g2⟩:= g2
  use u1++v1, v2++u2;
  simp only [g1, g2, append_assoc]

--#eval contains "aaabcfeffG".data (Pattern.ListChar "TH".data)

/-
Function: find
From: str::core::find
Description: https://doc.rust-lang.org/std/primitive.str.html#method.find
-/

def find_substring_aux (s: Str) (ss: Str) (i: Nat): Option Nat:= match s, ss with
  | _ , [] => some i
  | [], _ => none
  | hs::ts, _ => if List.isPrefixOf ss s then i else find_substring_aux ts ss (i + Char.utf8Size hs)

def find_substring (s: Str) (ss: Str) := find_substring_aux s ss 0

def is_substringpos (s: Str) (ss: Str) (i: Nat):= ∃ s0 s2, (s = s0 ++ ss ++ s2) ∧ (byteSize s0 = i)

def is_first_substringpos (s: Str) (ss: Str) (i: Nat) := (is_substringpos s ss i) ∧ (∀ j, is_substringpos s ss j → j ≥ i)

lemma find_substring_aux_none_sound:  find_substring_aux s ss l = none ↔  ¬ contains_substring s ss :=by
  induction s generalizing ss l
  cases ss; simp only [find_substring, find_substring_aux, not_false_eq_true, not_sym,
    Bool.not_eq_true, IsEmpty.forall_iff]
  constructor; simp only [IsEmpty.forall_iff];
  simp only [contains_substring, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  simp only [find_substring, find_substring_aux, Bool.not_eq_true, forall_true_left]
  simp only [contains_substring]
  rename_i h t ind
  cases ss; simp only [find_substring, find_substring_aux, not_false_eq_true, not_sym,
    Bool.not_eq_true, IsEmpty.forall_iff]
  constructor; simp only [IsEmpty.forall_iff]
  simp only [contains_substring, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i hs1 ts1
  simp only [find_substring, find_substring_aux, zero_add, Bool.not_eq_true]
  split; constructor; simp only [IsEmpty.forall_iff]
  rename_i gi; have gi:= contains_substring_of_isPrefixOf gi;
  simp only [gi, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i gi; simp only [contains_substring, gi, ↓reduceIte]
  simp only [Bool.not_eq_true] at ind; exact ind

theorem find_substring_none_sound:  find_substring s ss = none ↔   ¬ contains_substring s ss :=by
  unfold find_substring; apply find_substring_aux_none_sound

lemma find_substring_aux_para1_sub (gxk: x ≤ k): find_substring_aux s ss k = some i → find_substring_aux s ss (k-x)= some (i-x) :=by
  induction s generalizing k
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [find_substring_aux, Option.some.injEq, find_substring]
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [find_substring_aux, not_false_eq_true, not_sym, find_substring, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [find_substring_aux, Option.some.injEq, find_substring];
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [find_substring_aux, find_substring, zero_add]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1;
  have : x ≤ k + Char.utf8Size h:= by linarith
  have g1:= ind this g1
  have : k + Char.utf8Size h - x = k - x + Char.utf8Size h := by omega
  rw[this] at g1; exact g1

lemma find_substring_aux_para1_add : find_substring_aux s ss k = some i → find_substring_aux s ss (k+x)= some (i+x) :=by
  induction s generalizing k
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [find_substring_aux, Option.some.injEq, find_substring]
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [find_substring_aux, not_false_eq_true, not_sym, find_substring, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [find_substring_aux, Option.some.injEq, find_substring];
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [find_substring_aux, find_substring, zero_add]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1; have g1:= ind g1
  have : k + x + Char.utf8Size h = k + Char.utf8Size h + x := by omega
  rw[this, g1]

lemma find_substring_aux_para1_elim : find_substring_aux s ss k = some i → find_substring s ss= some (i-k):= by
  unfold find_substring;
  have : 0 = k - k := by simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le] ;
  rw[this]; apply find_substring_aux_para1_sub; simp only [le_refl]

lemma find_substring_aux_para1_le: find_substring_aux s ss k = some i → i ≥ k := by
  induction s generalizing k
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [find_substring_aux, Option.some.injEq, find_substring]
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [find_substring_aux, not_false_eq_true, not_sym, find_substring, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [find_substring_aux, Option.some.injEq, find_substring];
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [find_substring_aux, find_substring, zero_add]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1; have g1:= ind g1 ; linarith

theorem find_substring_some_sound: find_substring s ss = some i ↔  is_first_substringpos s ss i :=by
  constructor
  induction s generalizing i
  cases ss; simp only [find_substring, find_substring_aux, Option.some.injEq];
  intro gs; rw[← gs]; unfold is_first_substringpos is_substringpos
  simp only [List.append_nil, nil_eq_append, byteSize, exists_and_right, exists_eq_right,
    exists_eq_left, byteSize_aux, ge_iff_le, _root_.zero_le, implies_true, forall_const, and_self]
  simp only [find_substring, find_substring_aux, not_false_eq_true, not_sym, is_first_substringpos,
    ge_iff_le, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss = []); rename_i gss
  simp only [find_substring, gss, find_substring_aux, Option.some.injEq];
  intro gs; rw[← gs]; unfold is_first_substringpos is_substringpos
  simp only [List.append_nil, byteSize, exists_and_right, ge_iff_le, _root_.zero_le,
    forall_exists_index, and_imp, implies_true, forall_const, and_true]
  use []; simp only [List.nil_append, exists_eq', byteSize, and_self]
  rename_i gss; simp only [find_substring, find_substring_aux, zero_add]
  split; simp only [Option.some.injEq]
  intro gi; rw[← gi]; unfold is_first_substringpos is_substringpos
  simp only [List.append_assoc, byteSize, exists_and_right, ge_iff_le, _root_.zero_le,
    forall_exists_index, and_imp, implies_true, forall_const, and_true]
  use []; simp only [List.nil_append, byteSize, and_true]
  rename_i gpr; rw[IsPrefix_isPrefixOf_EQ] at gpr; unfold List.IsPrefix at gpr; obtain ⟨l, gl⟩ := gpr
  use l ; simp only [gl]; intro gs; have gs:= ind (find_substring_aux_para1_elim gs)
  unfold is_first_substringpos is_substringpos
  unfold is_first_substringpos is_substringpos at gs
  constructor
  obtain ⟨s0, s2, gsl⟩ := gs.left
  use h::s0, s2; simp only [cons_append, List.append_assoc, cons.injEq, true_and, byteSize, gsl]
  rename_i gs0; have gs0:= find_substring_aux_para1_le gs0; omega
  intro j gj;  obtain ⟨s0, s2, gsl⟩ := gs.left; obtain ⟨s00, s22, g02⟩ := gj
  have gsr:= gs.right (j-Char.utf8Size h)
  cases s00; rename_i gl _; rw[IsPrefix_isPrefixOf_EQ] at gl
  have : List.IsPrefix ss (h::t) := by simp only [g02, List.nil_append, prefix_append]
  contradiction
  rename_i hs0 ts0;
  simp only [cons_append, List.append_assoc, cons.injEq, byteSize, zero_add] at g02
  have: ∃ s0 s2, t = s0 ++ ss ++ s2 ∧ byteSize s0 = j - Char.utf8Size h := by
    use ts0, s22; simp only [g02, List.append_assoc, byteSize, true_and]
    omega
  have gsr:= gsr this ; rw[g02.left.left] at gsr; omega
  --mpr
  induction s generalizing i
  intro g ; cases ss; unfold find_substring find_substring_aux
  unfold is_first_substringpos at g; have g:= g.left; unfold is_substringpos at g
  obtain ⟨s0, s2, g⟩:=g; simp only [List.append_nil, nil_eq_append, byteSize] at g
  simp [g.left.left] at g; simp only [g.right]
  rename_i hs1 ts1 ; unfold is_first_substringpos at g;
  have g:= g.left; unfold is_substringpos at g
  obtain ⟨s0, s2, g⟩:=g; simp only [List.append_assoc, cons_append, nil_eq_append, and_false,
    not_false_eq_true, not_sym, byteSize, false_and] at g
  rename_i h t ind
  intro g; unfold is_first_substringpos is_substringpos at g;
  obtain ⟨s0, s2, gl⟩:=g.left; have g:= g.right
  unfold find_substring find_substring_aux
  by_cases (ss=[]) ; rename_i gss; rw[gss]
  simp only [Option.some.injEq]; rw[gss] at g
  have : ∃ s0 s2, h :: t = s0 ++ [] ++ s2 ∧ byteSize s0 = 0 :=by
    use [], h::t; simp only [List.append_nil, List.nil_append, byteSize, byteSize_aux, and_self]
  have g:= g 0 this ; omega ; rename_i gss
  simp only [contains_substring.match_1.eq_3, zero_add]; split; rename_i gi
  have gi:= IsPrefix_isPrefixOf_EQ.mp gi; unfold List.IsPrefix at gi; obtain ⟨u, gi⟩:= gi
  have : ∃ s0 s2, h :: t = s0 ++ ss ++ s2 ∧ byteSize s0 = 0 := by
    use [], u ; simp only [List.nil_append, gi, byteSize, byteSize_aux, and_self]
  have g:= g 0 this ; simp only [Option.some.injEq]; omega
  have : (is_first_substringpos t ss (i - Char.utf8Size h)) ∧ (i ≥ Char.utf8Size h) := by
    rename_i gi; cases s0;
    have gc: List.IsPrefix ss (h::t) := by unfold List.IsPrefix; use s2; simp only [gl.left,List.nil_append]
    have gc:= IsPrefix_isPrefixOf_EQ.mpr gc; contradiction
    rename_i hs0 ts0; simp only [cons_append, List.append_assoc, cons.injEq, zero_add, byteSize_cons] at gl
    have : i ≥ Char.utf8Size h:= by rw[gl.left.left]; omega
    simp only [ge_iff_le, this, and_true]
    unfold is_first_substringpos is_substringpos
    constructor; use ts0, s2;
    simp only [gl, List.append_assoc, byteSize, true_and]; omega
    intro i0 gu; obtain ⟨u0,u2,gu⟩:=gu
    have : ∃ s0 s2, h :: t = s0 ++ ss ++ s2 ∧ byteSize s0 = i0 + Char.utf8Size h := by
      use h::u0, u2; simp only [gu, List.append_assoc, cons_append, zero_add, true_and, byteSize_cons, add_comm]
    have g:= g (i0 + Char.utf8Size h) this; omega
  have ind:=ind this.left; unfold find_substring at ind
  have e: find_substring_aux t ss (0 + Char.utf8Size h) = some (i - Char.utf8Size h + Char.utf8Size h):= find_substring_aux_para1_add ind
  have : i - Char.utf8Size h + Char.utf8Size h = i := by omega
  simp only [zero_add, this] at e; exact e



--#eval find_substring "Löwe 老虎 Léopard Gepardi".data "pard".data

def find_char_filter_aux (s: Str) (f: Char → Bool) (i: Nat) : Option Nat:= match s with
  | [] => none
  | h::t => if f h then some i else find_char_filter_aux t f (i + Char.utf8Size h)

def find_char_filter (s: Str) (f: Char → Bool)  := find_char_filter_aux s f 0

def is_char_filter_pos (s: Str) (f: Char → Bool) (i: Nat) := ∃ s0 c s2, (s = s0 ++ [c] ++ s2) ∧ (f c) ∧ (byteSize s0 = i)

def is_first_char_filter_pos (s: Str) (f: Char → Bool) (i: Nat) := (is_char_filter_pos s f i) ∧ (∀ j, is_char_filter_pos s f j → j ≥ i)

lemma find_char_filter_aux_none_sound: find_char_filter_aux s f i = none ↔  ∀ x ∈ s, ¬ f x :=by
  induction s generalizing i
  simp only [find_char_filter_aux, not_mem_nil, Bool.not_eq_true, IsEmpty.forall_iff, forall_const,
    forall_true_left]
  rename_i h t ind
  simp only [find_char_filter_aux, mem_cons, Bool.not_eq_true, forall_eq_or_imp]
  split; rename_i gf; simp only [gf, not_false_eq_true, not_sym, false_and]
  rename_i g; simp only [g, true_and];
  simp only [Bool.not_eq_true] at ind; apply ind

theorem find_char_filter_none_sound: find_char_filter s f = none ↔  ∀ x ∈ s, ¬ f x :=by
  unfold find_char_filter; apply find_char_filter_aux_none_sound

lemma find_char_filter_aux_para1_sub (gxk: x ≤ k): find_char_filter_aux s f k = some i → find_char_filter_aux s f (k-x)= some (i-x) :=by
  induction s generalizing k
  simp only [find_char_filter_aux, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ind
  simp only [find_char_filter_aux]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1;
  have : x ≤ k + Char.utf8Size h:= by linarith
  have g1:= ind this g1
  have : k + Char.utf8Size h - x = k - x + Char.utf8Size h := by omega
  rw[this] at g1; exact g1

lemma find_char_filter_aux_para1_add : find_char_filter_aux s f k = some i → find_char_filter_aux s f (k+x)= some (i+x) :=by
  induction s generalizing k
  simp only [find_char_filter_aux, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ind
  simp only [find_char_filter_aux]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1; have g1:= ind g1
  have : k + x + Char.utf8Size h= k + Char.utf8Size h + x := by omega
  rw[this]; exact g1

lemma find_char_filter_aux_para1_elim : find_char_filter_aux s f k = some i → find_char_filter s f= some (i-k):= by
  unfold find_char_filter;
  have : 0 = k - k := by simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le] ;
  rw[this]; apply find_char_filter_aux_para1_sub; simp only [le_refl]

lemma find_char_filter_aux_para1_le: find_char_filter_aux s f k = some i → i ≥ k := by
  induction s generalizing k
  simp only [find_char_filter_aux, not_false_eq_true, not_sym, ge_iff_le, IsEmpty.forall_iff]
  rename_i h t ind
  simp only [find_char_filter_aux, ge_iff_le]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1; have g1:= ind g1 ; linarith

theorem find_char_filter_some_sound: find_char_filter s f = some i ↔ is_first_char_filter_pos s f i :=by
  induction s generalizing i
  unfold find_char_filter find_char_filter_aux;
  simp only [not_false_eq_true, not_sym, is_first_char_filter_pos, is_char_filter_pos,
    List.append_assoc, singleton_append, nil_eq_append, and_false, false_and, exists_const,
    ge_iff_le, IsEmpty.forall_iff, forall_const, and_true]
  rename_i h t ind
  constructor
  unfold find_char_filter find_char_filter_aux
  split; simp only [Option.some.injEq];
  intro gs; rw[← gs]; unfold is_first_char_filter_pos is_char_filter_pos
  simp only [List.append_assoc, singleton_append, byteSize, exists_and_right, ge_iff_le,
    _root_.zero_le, forall_exists_index, and_imp, implies_true, forall_const, and_true]
  use []; simp only [List.nil_append, cons.injEq, exists_and_left, exists_eq', and_true,
    byteSize, exists_eq_left']; assumption
  rename_i gs1; simp only [zero_add]
  intro gs; have gs:= ind.mp (find_char_filter_aux_para1_elim gs);
  unfold is_first_char_filter_pos is_char_filter_pos
  unfold is_first_char_filter_pos is_char_filter_pos at gs
  constructor
  obtain ⟨s0, c, s2, gsl⟩ := gs.left
  use h::s0, c,  s2;
  simp only [gsl, List.append_assoc, singleton_append, cons_append, byteSize, byteSize_aux,
    zero_add, true_and]
  rename_i gs0; have gs0:= find_char_filter_aux_para1_le gs0; omega
  intro j gj;  obtain ⟨s0, c, _, _⟩ := gs.left; obtain ⟨s00, c0, s22, g02⟩ := gj
  have gsr:= gs.right (j-Char.utf8Size h)
  cases s00; simp only [List.nil_append, singleton_append, cons.injEq, byteSize, byteSize_aux] at g02
  rw [g02.left.left, g02.right.left] at gs1
  contradiction
  rename_i hs0 ts0;
  simp only [cons_append, List.append_assoc, cons.injEq, byteSize, byteSize_aux, zero_add] at g02
  have: ∃ s0 c s2, t = s0 ++ [c] ++ s2 ∧ f c = true ∧ byteSize s0 = j - Char.utf8Size h := by
    use ts0, c0, s22; simp only [g02, List.nil_append, List.append_assoc, singleton_append,
      byteSize, true_and]
    omega
  have gsr:= gsr this ; rw[g02.left.left] at gsr; omega
  -- mpr
  unfold is_first_char_filter_pos is_char_filter_pos find_char_filter find_char_filter_aux
  intro g; split; simp only [Option.some.injEq]
  have : ∃ s0 c s2, h :: t = s0 ++ [c] ++ s2 ∧ f c = true ∧ byteSize s0 = 0 :=by
    use [], h, t; rename_i gf; simp only [List.nil_append, singleton_append, gf, true_and, byteSize, byteSize_aux]
  have gi:= g.right 0 this; omega
  have : (is_first_char_filter_pos t f (i - Char.utf8Size h)) ∧ (i ≥ Char.utf8Size h) :=by
    unfold is_first_char_filter_pos is_char_filter_pos
    obtain ⟨u1, c, u2, gl⟩ := g.left
    cases u1; simp only [List.nil_append, singleton_append, cons.injEq] at gl
    rename_i gf; rw[gl.left.left, gl.right.left] at gf; contradiction
    simp only [cons_append, List.append_assoc, singleton_append, cons.injEq, byteSize_cons] at gl
    rename_i hu tu; constructor ; constructor
    use tu, c, u2; simp only [gl, List.nil_append, List.append_assoc,
      singleton_append, true_and]; omega
    intro i0 gi0; obtain ⟨u1, c, u2, gu⟩ := gi0
    have : ∃ s0 c s2, h :: t = s0 ++ [c] ++ s2 ∧ f c = true ∧ byteSize s0 = i0 + Char.utf8Size h := by
      use h::u1, c, u2; simp only [gu, List.append_assoc, singleton_append, cons_append,
        byteSize_cons, true_and]; omega
    have g:= g.right (i0 + Char.utf8Size h) this; omega
    rw[gl.left.left]; omega
  have ind:= ind.mpr this.left
  have: find_char_filter_aux t f (0 + Char.utf8Size h) = some (i - Char.utf8Size h + Char.utf8Size h):= by
    unfold find_char_filter at ind ; apply find_char_filter_aux_para1_add ind
  rw[this]; simp only [Option.some.injEq] ; omega


def find (s: Str) (P: Pattern) : Option Nat := match P with
  | Pattern.SingleChar c => find_char_filter s (fun x => x = c)
  | Pattern.ListChar l => find_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => find_char_filter s f
  | Pattern.WholeString ss => find_substring s ss

/-
Function: rfind
From: str::core::rfind
Description: https://doc.rust-lang.org/std/primitive.str.html#method.rfind
-/

def is_last_substringpos (s: Str) (ss: Str) (i: Nat) := (is_substringpos s ss i) ∧ (∀ j, is_substringpos s ss j → j ≤ i)

def is_last_char_filter_pos (s: Str) (f: Char → Bool) (i: Nat) := (is_char_filter_pos s f i) ∧ (∀ j, is_char_filter_pos s f j → j ≤ i)

def rfind_substring (s: Str) (ss: Str) := match find_substring (List.reverse s) (List.reverse ss) with
  | none => none
  | some i => some (byteSize s - byteSize ss -i)

lemma is_substring_reverse: contains_substring s ss = contains_substring (reverse s) (reverse ss) :=by
  by_cases contains_substring s ss
  rename_i g; rw[g]; symm; rw[contains_substring_EQ]; unfold contains_substring_def
  rw[contains_substring_EQ] at g; unfold contains_substring_def at g; obtain ⟨u1, u2, gu⟩:=g
  have: reverse s = (reverse u2) ++ (reverse ss) ++ (reverse u1) :=by
    rw[gu]; simp only [List.append_assoc, reverse_append]
  rw[this]; use reverse u2, reverse u1
  rename_i g;
  have : ¬ contains_substring (reverse s) (reverse ss) :=by
    rw[contains_substring_EQ]; unfold contains_substring_def
    rw[contains_substring_EQ] at g; unfold contains_substring_def at g;
    by_contra; rename_i gc; obtain ⟨u1, u2, gu⟩:=gc
    have: s = reverse (reverse s) :=by simp only [reverse_reverse]
    have: s = (reverse u2) ++ ss ++ (reverse u1) :=by
      rw[this, gu]; simp only [List.append_assoc, reverse_append, reverse_reverse]
    have: s = (reverse u2) ++ (ss ++ (reverse u1)) :=by simp only [this, List.append_assoc]
    simp only [List.append_assoc, not_exists] at g
    have: ¬s = (reverse u2) ++ (ss ++ reverse u1) := by apply g
    contradiction
  simp only [g, this]


theorem rfind_substring_none_sound: rfind_substring s ss = none ↔  ¬ contains_substring s ss := by
  unfold rfind_substring; split; simp only [Bool.not_eq_true, forall_true_left]
  rename_i g ; have g:= find_substring_none_sound.mp g
  rw [is_substring_reverse];
  simp only [g]; simp only [byteSize, not_false_eq_true, not_sym,
    Bool.not_eq_true, IsEmpty.forall_iff]
  rename_i g;
  have g: ¬  find_substring (reverse s) (reverse ss) = none:= by simp only [g, not_false_eq_true, not_sym]
  rw[find_substring_none_sound] at g; simp only [Bool.not_eq_true, Bool.not_eq_false] at g
  rw[← is_substring_reverse] at g; simp only [g, not_false_eq_true, not_sym]


lemma is_substringpos_reverse: is_substringpos s ss i →  is_substringpos (reverse s) (reverse ss) (byteSize s - byteSize ss - i) :=by
  unfold is_substringpos;
  intro g; obtain ⟨u1, u2, gu⟩ :=g
  have : reverse s = (reverse u2) ++ (reverse ss) ++ (reverse u1) :=by
    rw[ gu.left]; simp only [List.append_assoc, reverse_append]
  use (reverse u2) , (reverse u1)
  simp only [this, List.append_assoc,  true_and]
  rw[byteSize_reverse]
  have: byteSize s = byteSize u1 + byteSize ss + byteSize u2 := by
    rw[gu.left, byteSize_concat, byteSize_concat]
  omega

--should not merge the two (because of Nat subtraction)
lemma is_substringpos_reverse_mpr: is_substringpos (reverse s) (reverse ss) i →  is_substringpos s ss (byteSize s - byteSize ss - i) :=by
  intro g; obtain ⟨u1, u2, gu⟩ :=g
  have: s = reverse (reverse s) :=by simp only [reverse_reverse]
  have : s = (reverse u2) ++ ss ++ (reverse u1) :=by
    rw[this, gu.left]; simp only [List.append_assoc, reverse_append, reverse_reverse]
  unfold is_substringpos
  use reverse u2, reverse u1; simp only [this, List.append_assoc,  true_and]
  rw[byteSize_reverse, byteSize_concat, byteSize_reverse, byteSize_concat,  byteSize_reverse]
  have : byteSize (reverse s) = byteSize (u1 ++ reverse ss) + byteSize u2 := by
    rw[gu.left, byteSize_concat]
  rw[byteSize_reverse, byteSize_concat, byteSize_reverse] at this
  omega

theorem rfind_substring_some_sound: rfind_substring s ss = some i ↔  is_last_substringpos s ss i := by
  constructor
  unfold rfind_substring; split; simp only [not_false_eq_true, not_sym, IsEmpty.forall_iff];
  simp only [Option.some.injEq]; intro gb;
  rename_i i0 gt g; have g:= find_substring_some_sound.mp g
  unfold is_last_substringpos ; unfold is_first_substringpos at g
  have gl:= g.left; have gr:=g.right
  constructor
  unfold is_substringpos at gl ; obtain ⟨u1, u2, gu⟩ := gl
  unfold is_substringpos
  have: s = reverse (reverse s) :=by simp only [reverse_reverse]
  have : s = (reverse u2) ++ ss ++ (reverse u1) :=by
    rw[this, gu.left]; simp only [List.append_assoc, reverse_append, reverse_reverse]
  use reverse u2, reverse u1; simp only [this, List.append_assoc,  true_and]
  rw[byteSize_reverse, ← gb, ← gu.right]
  have : byteSize (reverse s) = byteSize (u1 ++ reverse ss) + byteSize u2 := by
    rw[gu.left, byteSize_concat]
  rw[byteSize_reverse, byteSize_concat, byteSize_reverse] at this
  omega
  intro j gj; have gi0:= is_substringpos_reverse gj
  have gr:= gr (byteSize s - byteSize ss - j) gi0
  unfold is_substringpos at gj ; obtain ⟨u1, u2, gu⟩ := gj
  have : byteSize s = byteSize u1 + byteSize ss + byteSize u2 :=by
    rw[gu.left, byteSize_concat, byteSize_concat]
  omega
  --mpr
  intro g ; unfold rfind_substring; split
  unfold is_last_substringpos at g; rename_i gh; have gh:= find_substring_none_sound.mp gh
  rw[contains_substring_EQ] at gh; unfold contains_substring_def at gh
  simp only [List.append_assoc, not_exists] at gh
  have gl := g.left; unfold is_substringpos at gl; obtain ⟨u1, u2, gl⟩ := gl
  have : reverse s = u2.reverse ++ (reverse ss ++ u1.reverse) := by
    simp only [gl, List.append_assoc, reverse_append]
  have gh:= gh u2.reverse u1.reverse; contradiction
  rename_i i0 gi0; have gi0:=find_substring_some_sound.mp gi0
  simp only [Option.some.injEq]
  unfold is_first_substringpos at gi0 ; unfold is_last_substringpos at g
  have g1:= gi0.right (byteSize s - byteSize ss - i) (is_substringpos_reverse g.left)
  have g2:= g.right (byteSize s - byteSize ss - i0) (is_substringpos_reverse_mpr gi0.left)
  have g:= g.left; unfold is_substringpos at g; obtain ⟨u1, u2, g⟩ := g
  have : byteSize s = byteSize u1 + byteSize ss + byteSize u2 :=by
    rw[g.left]; simp only [List.append_assoc, byteSize_concat]; omega
  omega


--this function return the position next to that of the first char satisfying the filter
def find_char_filter_next_aux (s: Str) (f: Char → Bool) (i: Nat) : Option Nat:= match s with
  | [] => none
  | h::t => if f h then some (i + Char.utf8Size h) else find_char_filter_next_aux t f (i + Char.utf8Size h)

--this function return the position next to that of the first char satisfying the filter
def find_char_filter_next (s: Str) (f: Char → Bool)  := find_char_filter_next_aux s f 0

def rfind_char_filter (s: Str) (f: Char → Bool)  := match find_char_filter_next (List.reverse s) f with
  | none => none
  | some i => some (byteSize s - i)

lemma find_char_filter_next_aux_none_eq: find_char_filter_next_aux s f i = none ↔  find_char_filter_aux s f i = none :=by
  induction s generalizing i
  unfold find_char_filter_next_aux find_char_filter_aux; simp only [forall_true_left]
  rename_i h t ind
  unfold find_char_filter_next_aux find_char_filter_aux; split; simp only [IsEmpty.forall_iff]
  exact ind

lemma find_char_filter_next_none_eq: find_char_filter_next s f = none ↔  find_char_filter s f = none :=by
  unfold find_char_filter_next find_char_filter ; apply find_char_filter_next_aux_none_eq

theorem rfind_char_filter_none_sound: rfind_char_filter s f = none ↔   ∀ x ∈ s, ¬ f x :=by
  unfold rfind_char_filter
  split; simp only [Bool.not_eq_true, forall_true_left];
  rename_i g; have g:= find_char_filter_none_sound.mp (find_char_filter_next_none_eq.mp g)
  simp_all only [mem_reverse, Bool.not_eq_true, implies_true, forall_const]
  simp only [byteSize, not_false_eq_true, not_sym, Bool.not_eq_true, IsEmpty.forall_iff]
  rename_i g; have g: ¬ find_char_filter_next (reverse s) f =  none := by simp only [g,not_false_eq_true, not_sym]
  rw[find_char_filter_next_none_eq, find_char_filter_none_sound] at g
  simp only [mem_reverse, Bool.not_eq_true, not_forall, Bool.not_eq_false, exists_prop] at g
  simp only [false_iff, not_forall, Bool.not_eq_false, exists_prop, g]


def is_find_char_filter_next (s: Str) (f: Char → Bool) (i: Nat) := ∃ s0 c s2, (s = s0 ++ [c] ++ s2) ∧ (f c) ∧ (byteSize s0 + Char.utf8Size c = i)

def is_first_find_char_filter_next (s: Str) (f: Char → Bool) (i: Nat) := (is_find_char_filter_next s f i) ∧ (∀ j, is_find_char_filter_next s f j → j ≥ i)

lemma is_char_filter_pos_reverse: is_char_filter_pos s f i → is_find_char_filter_next (reverse s) f (byteSize s - i) :=by
  unfold is_char_filter_pos is_find_char_filter_next
  intro g; obtain ⟨u1, c, u2, gu⟩ := g
  have : reverse s = (reverse u2) ++ [c] ++ (reverse u1) :=by
    rw[ gu.left]; simp only [List.append_assoc, singleton_append, reverse_append, reverse_cons]
  use (reverse u2) , c,  (reverse u1)
  simp only [this, List.append_assoc,   true_and]
  rw[byteSize_reverse]; simp only [gu.right.left, true_and]
  have: byteSize s = byteSize u1 + Char.utf8Size c + byteSize u2 := by
    rw[gu.left]; simp only [List.append_assoc, singleton_append, byteSize_concat, byteSize]; omega
  omega
--should not merge the two
lemma is_char_filter_pos_reverse_mpr: is_find_char_filter_next (reverse s) f i → is_char_filter_pos s f (byteSize s - i) :=by
  unfold is_char_filter_pos is_find_char_filter_next
  intro g; obtain ⟨u1, c, u2, gu⟩ := g
  have : reverse s.reverse = (reverse u2) ++ [c] ++ (reverse u1) :=by
    rw[ gu.left]; simp only [List.append_assoc, singleton_append, reverse_append, reverse_cons]
  use (reverse u2) , c,  (reverse u1)
  simp only [this, List.append_assoc,   true_and]
  rw[byteSize_reverse]; simp only [reverse_reverse, List.append_assoc, singleton_append] at this
  simp only [this, singleton_append, gu, byteSize_concat, byteSize_reverse, byteSize_cons, true_and]
  have: byteSize s = byteSize u1 + Char.utf8Size c + byteSize u2 := by
    rw[this]; simp only [byteSize_concat, byteSize_reverse, byteSize_cons]; omega
  omega


lemma rfind_char_filter_aux_para1_sub (gxk: x ≤ k): find_char_filter_next_aux s f k = some i → find_char_filter_next_aux s f (k-x)= some (i-x) :=by
  induction s generalizing k
  simp only [find_char_filter_next_aux, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ind
  simp only [find_char_filter_next_aux]
  split; simp only [Option.some.injEq]; intro gk; omega
  intro g1;
  have : x ≤ k + Char.utf8Size h:= by linarith
  have g1:= ind this g1
  have : k + Char.utf8Size h - x = k - x + Char.utf8Size h := by omega
  rw[this] at g1; exact g1

lemma rfind_char_filter_aux_para1_elim : find_char_filter_next_aux s f k = some i → find_char_filter_next s f= some (i-k):= by
  unfold find_char_filter_next;
  have : 0 = k - k := by simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le] ;
  rw[this]; apply rfind_char_filter_aux_para1_sub; simp only [le_refl]

lemma rfind_char_filter_aux_para1_le: find_char_filter_next_aux s f k = some i → i ≥ k := by
  induction s generalizing k
  simp only [find_char_filter_next_aux, not_false_eq_true, not_sym, ge_iff_le, IsEmpty.forall_iff]
  rename_i h t ind
  simp only [find_char_filter_next_aux, ge_iff_le]
  split; simp only [Option.some.injEq]; intro gk; linarith
  intro g1; have g1:= ind g1 ; linarith

lemma find_char_filter_next_is_first: find_char_filter_next s f = some i →  is_first_find_char_filter_next s f i :=by
  induction s generalizing i
  unfold find_char_filter_next find_char_filter_next_aux;
  simp only [not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ind
  unfold find_char_filter_next find_char_filter_next_aux
  split; simp only [Option.some.injEq]
  intro gs; simp only [zero_add] at gs; rw[← gs]; unfold is_first_find_char_filter_next is_find_char_filter_next
  constructor; use [], h, t; rename_i g; simp only [List.nil_append, singleton_append, g, byteSize,
    byteSize_aux, zero_add, and_self]
  intro i0 gi0; obtain ⟨u1, c, u2, gu⟩ := gi0
  cases u1; simp only [List.nil_append, singleton_append, cons.injEq, byteSize, byteSize_aux,
    zero_add] at gu; rw[gu.left.left, gu.right.right]; simp only [ge_iff_le]
  rename_i hu1 tu1; simp only [cons_append, List.append_assoc, singleton_append, cons.injEq, zero_add] at gu
  rw[byteSize_cons, ←  gu.left.left] at gu; linarith
  intro gs; simp only [zero_add] at gs; rename_i gs1
  have gs:= ind (rfind_char_filter_aux_para1_elim gs);
  unfold is_first_find_char_filter_next is_find_char_filter_next
  unfold is_first_find_char_filter_next is_find_char_filter_next at gs
  constructor
  obtain ⟨s0, c, s2, gsl⟩ := gs.left
  use h::s0, c,  s2;
  simp only [gsl, List.append_assoc, singleton_append, cons_append, byteSize, byteSize_aux,
    zero_add, true_and]
  rename_i gs0; have gs0:= rfind_char_filter_aux_para1_le gs0; omega
  intro j gj;  obtain ⟨s0, c, _, _⟩ := gs.left; obtain ⟨s00, c0, s22, g02⟩ := gj
  have gsr:= gs.right (j-Char.utf8Size h)
  cases s00; simp only [List.nil_append, singleton_append, cons.injEq, byteSize, byteSize_aux] at g02
  rw [g02.left.left, g02.right.left] at gs1
  contradiction
  rename_i hs0 ts0;
  simp only [cons_append, List.append_assoc, cons.injEq, byteSize, byteSize_aux, zero_add] at g02
  have: ∃ s0 c s2, t = s0 ++ [c] ++ s2 ∧ f c = true ∧ byteSize s0 + Char.utf8Size c = j - Char.utf8Size h := by
    use ts0, c0, s22; simp only [g02, List.nil_append, List.append_assoc, singleton_append,
      byteSize, true_and]
    omega
  have gsr:= gsr this ; rw[g02.left.left] at gsr; omega

theorem rfind_char_filter_some_sound: rfind_char_filter s f = some i ↔ is_last_char_filter_pos s f i :=by
  constructor
  unfold rfind_char_filter
  split; simp only [not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i g; have g:= find_char_filter_next_is_first g
  simp only [Option.some.injEq]; intro gb; rename_i i0 gt
  unfold is_last_char_filter_pos;
  unfold is_first_char_filter_pos at g
  have gl:= g.left; have gr:=g.right
  constructor
  unfold is_char_filter_pos at gl ; obtain ⟨u1, u, u2, gu⟩ := gl
  unfold is_char_filter_pos
  have: s = reverse (reverse s) :=by simp only [reverse_reverse]
  have : s = (reverse u2) ++ [u] ++ (reverse u1) :=by
    rw[this, gu.left]; simp only [List.append_assoc, singleton_append, reverse_append, reverse_cons]
  use reverse u2, u, reverse u1; simp only [this, gu, List.append_assoc,  true_and]
  rw[byteSize_reverse, ← gb, ← gu.right.right]
  have : byteSize (reverse s) = byteSize (u1 ++ [u]) + byteSize u2 := by
    rw[gu.left, byteSize_concat]
  have e1: byteSize [u] = Char.utf8Size u :=by simp only [byteSize, add_zero]
  rw[byteSize_reverse, byteSize_concat, e1] at this
  omega
  intro j gj; have gi0:= is_char_filter_pos_reverse gj
  have gr:= gr (byteSize s - j) gi0
  unfold is_char_filter_pos at gj ; obtain ⟨u1, c, u2, gu⟩ := gj
  have : byteSize s = byteSize u1 + Char.utf8Size c + byteSize u2 :=by
    rw [gu.left]; simp only [List.append_assoc, singleton_append, byteSize_concat, byteSize] ; omega
  omega
  intro g
  unfold rfind_char_filter; split;
  rename_i gn; rw[find_char_filter_next_none_eq, find_char_filter_none_sound] at gn
  unfold is_last_char_filter_pos at g; simp only [mem_reverse, Bool.not_eq_true] at gn
  have gl:=g.left; unfold is_char_filter_pos at gl; obtain ⟨u1, c, u2, gl⟩:= gl
  have : c ∈  s := by simp only [gl, List.append_assoc, singleton_append, mem_append, mem_cons,
    true_or, or_true]
  have gn:=gn c this; rw[gl.right.left] at gn; contradiction
  rename_i i0 gi0; simp only [Option.some.injEq]; have gi0:= find_char_filter_next_is_first gi0
  unfold is_first_find_char_filter_next at gi0; unfold is_last_char_filter_pos at g
  have g1:= gi0.right (byteSize s - i) (is_char_filter_pos_reverse g.left)
  have g2:= g.right (byteSize s - i0) (is_char_filter_pos_reverse_mpr gi0.left)
  have gl:=g.left; unfold is_char_filter_pos at gl; obtain ⟨u1, c, u2, gl⟩:= gl
  have : byteSize s = byteSize u1 + Char.utf8Size c + byteSize u2:= by
    rw[gl.left]; simp only [List.append_assoc, singleton_append, byteSize_concat, byteSize_cons]; omega
  omega


def rfind (s: Str) (P: Pattern) : Option Nat := match P with
  | Pattern.SingleChar c => rfind_char_filter s (fun x => x = c)
  | Pattern.ListChar l => rfind_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => rfind_char_filter s f
  | Pattern.WholeString ss => rfind_substring s ss


/-
Useful definitions for stating the soundness theorem of functions in "split" family
Not in Rust library
-/

--convert char index to byte index (position)
def charIndex_to_pos (s: Str) (i: Nat)  :=
  if i = 0 then 0 else match s with
  | [] => 0
  | h::t => (Char.utf8Size h) + charIndex_to_pos t (i-1)

def charIndex_to_pos_def (s: Str) (i: Nat)  := byteSize (s.take i)

theorem charIndex_to_pos_EQ: charIndex_to_pos s i  = charIndex_to_pos_def s i  :=by
  induction s generalizing i
  unfold charIndex_to_pos charIndex_to_pos_def take
  split; rename_i gh; simp only [gh, byteSize];
  simp only; split; simp only [byteSize]; simp only [byteSize];
  rename_i g _; simp only [succ_eq_add_one, length_nil, not_lt_zero'] at g
  rename_i h t ind
  unfold charIndex_to_pos charIndex_to_pos_def take
  split; rename_i gh; simp only [gh, byteSize];
  simp only; split; contradiction; rename_i u _; simp only [not_false_eq_true, not_sym] at u
  rename_i n h1 t1 g1 _; simp only [cons.injEq] at g1; rw[← g1.left, ← g1.right, byteSize]
  simp only [succ_eq_add_one, add_tsub_cancel_right, add_right_inj]
  rw[@ind n, charIndex_to_pos_def]

--return the first char index of ss in s if ss is a substring of s, return none otherwise
def substring_charIndex_aux (s: Str) (ss: Str) (i: Nat): Option Nat:= match s, ss with
  | _ , [] => some i
  | [], _ => none
  | _::ts, _ => if List.isPrefixOf ss s then i else substring_charIndex_aux ts ss (i + 1)

def substring_charIndex (s: Str) (ss: Str) := substring_charIndex_aux s ss 0

def is_substringcharIndex (s: Str) (ss: Str) (i: Nat):= ∃ s0 s2, (s = s0 ++ ss ++ s2) ∧ (length s0 = i)

def is_first_substringcharIndex (s: Str) (ss: Str) (i: Nat) := (is_substringcharIndex s ss i) ∧ (∀ j, is_substringcharIndex s ss j → j ≥ i)

lemma sub_substring_charIndex_none_sound:  substring_charIndex_aux s ss l = none →  ¬ contains_substring s ss :=by
  induction s generalizing ss l
  cases ss; simp only [substring_charIndex, substring_charIndex_aux, not_false_eq_true, not_sym,
    Bool.not_eq_true, IsEmpty.forall_iff]
  simp only [substring_charIndex, substring_charIndex_aux, Bool.not_eq_true, forall_true_left]
  simp only [contains_substring, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ind
  cases ss; simp only [find_substring, substring_charIndex_aux, not_false_eq_true, not_sym,
    Bool.not_eq_true, IsEmpty.forall_iff]
  rename_i hs1 ts1
  simp only [substring_charIndex, substring_charIndex_aux, zero_add, Bool.not_eq_true]
  split; simp only [IsEmpty.forall_iff]
  intro gs; rename_i gl; simp only [contains_substring, gl, not_false_eq_true, not_sym, ↓reduceIte]
  have gs:= ind gs; simp only [Bool.not_eq_true] at gs; exact gs

lemma substring_charIndex_none_sound:  substring_charIndex s ss = none →  ¬ contains_substring s ss :=by
  unfold substring_charIndex; apply sub_substring_charIndex_none_sound

lemma sub_substring_charIndex_some_sound10 (gxk: x ≤ k): substring_charIndex_aux s ss k = some i → substring_charIndex_aux s ss (k-x)= some (i-x) :=by
  induction s generalizing k
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [substring_charIndex_aux, Option.some.injEq, find_substring]
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [substring_charIndex_aux, not_false_eq_true, not_sym, find_substring, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [substring_charIndex_aux, Option.some.injEq, find_substring];
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [substring_charIndex_aux, find_substring, zero_add]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1;
  have : x ≤ k + 1:= by linarith
  have g1:= ind this g1
  have : k + 1 - x = k - x + 1 := by omega
  rw[this] at g1; exact g1

lemma sub_substring_charIndex_some_sound_mpr: substring_charIndex_aux s ss k = some i → substring_charIndex_aux s ss (k+x)= some (i+x) :=by
  induction s generalizing k
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [substring_charIndex_aux, Option.some.injEq, find_substring]
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [substring_charIndex_aux, not_false_eq_true, not_sym, find_substring, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [substring_charIndex_aux, Option.some.injEq, find_substring];
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [substring_charIndex_aux, find_substring, zero_add]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1;
  have g1:= ind g1; have:  k + x + 1 = k + 1 + x := by omega
  rw[this, g1]

lemma sub_substring_charIndex_some_sound1 : substring_charIndex_aux s ss k = some i → substring_charIndex s ss= some (i-k):= by
  unfold substring_charIndex;
  have : 0 = k - k := by simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le] ;
  rw[this]; apply sub_substring_charIndex_some_sound10; simp only [le_refl]

lemma sub_substring_charIndex_some_sound2: substring_charIndex_aux s ss k = some i → i ≥ k := by
  induction s generalizing k
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [substring_charIndex_aux, Option.some.injEq, find_substring]
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [substring_charIndex_aux, not_false_eq_true, not_sym, find_substring, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss=[]); rename_i gss; rw[gss]
  simp only [substring_charIndex_aux, Option.some.injEq, find_substring];
  intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [substring_charIndex_aux, find_substring, zero_add]
  split; simp only [Option.some.injEq]; intro gk; simp only [gk, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  intro g1; have g1:= ind g1 ; linarith

theorem substring_charIndex_some_sound: substring_charIndex s ss = some i ↔  is_first_substringcharIndex s ss i :=by
  constructor
  induction s generalizing i
  cases ss; simp only [substring_charIndex, substring_charIndex_aux, Option.some.injEq];
  intro gs; rw[← gs]; unfold is_first_substringcharIndex is_substringcharIndex
  simp only [List.append_nil, nil_eq_append, exists_and_right, exists_eq_right, exists_eq_left,
    length_nil, ge_iff_le, _root_.zero_le, implies_true, forall_const, and_self]
  simp only [substring_charIndex, substring_charIndex_aux, not_false_eq_true, not_sym, is_first_substringcharIndex,
    ge_iff_le, IsEmpty.forall_iff]
  rename_i h t ind
  by_cases (ss = []); rename_i gss
  simp only [substring_charIndex, gss, substring_charIndex_aux, Option.some.injEq];
  intro gs; rw[← gs]; unfold is_first_substringcharIndex is_substringcharIndex
  simp only [List.append_nil, byteSize, exists_and_right, ge_iff_le, _root_.zero_le,
    forall_exists_index, and_imp, implies_true, forall_const, and_true]
  use []; simp only [List.nil_append, exists_eq', length_nil, and_self]
  rename_i gss; simp only [substring_charIndex, substring_charIndex_aux, zero_add]
  split; simp only [Option.some.injEq]
  intro gi; rw[← gi]; unfold is_first_substringcharIndex is_substringcharIndex
  simp only [List.append_assoc, byteSize, exists_and_right, ge_iff_le, _root_.zero_le,
    forall_exists_index, and_imp, implies_true, forall_const, and_true]
  use []; simp only [List.nil_append, byteSize_aux, and_true]
  rename_i gpr; rw[IsPrefix_isPrefixOf_EQ] at gpr; unfold List.IsPrefix at gpr; obtain ⟨l, gl⟩ := gpr
  simp only [length_nil, and_true]
  use l ; simp only [gl]; intro gs; have gs:= ind (sub_substring_charIndex_some_sound1 gs)
  unfold is_first_substringcharIndex is_substringcharIndex
  unfold is_first_substringcharIndex is_substringcharIndex at gs
  constructor
  obtain ⟨s0, s2, gsl⟩ := gs.left
  use h::s0, s2; simp only [gsl, List.append_assoc, cons_append, length_cons, true_and]
  rename_i gs0; have gs0:= sub_substring_charIndex_some_sound2 gs0; omega
  intro j gj;  obtain ⟨s0, s2, gsl⟩ := gs.left; obtain ⟨s00, s22, g02⟩ := gj
  have gsr:= gs.right (j-1)
  cases s00; rename_i gl _; rw[IsPrefix_isPrefixOf_EQ] at gl
  have : List.IsPrefix ss (h::t) := by simp only [g02, List.nil_append, prefix_append]
  contradiction
  rename_i hs0 ts0;
  simp only [cons_append, List.append_assoc, cons.injEq, length_cons] at g02
  have: ∃ s0 s2, t = s0 ++ ss ++ s2 ∧ s0.length = j - 1 := by
    use ts0, s22; simp only [g02, List.append_assoc, byteSize, true_and]
    omega
  have gsr:= gsr this ; omega
  --mpr
  induction s generalizing i
  intro g; unfold substring_charIndex substring_charIndex_aux
  cases ss; simp only [Option.some.injEq]; unfold is_first_substringcharIndex is_substringcharIndex at g
  obtain ⟨u1, u2, gu⟩ := g.left
  simp only [List.append_nil, nil_eq_append] at gu; rw[gu.left.left] at gu
  simp only [true_and, length_nil] at gu; exact gu.right
  simp only [not_false_eq_true, not_sym]; rename_i hs1 ts1
  unfold is_first_substringcharIndex is_substringcharIndex at g
  obtain ⟨u1, u2, gu⟩ := g.left; simp only [List.append_assoc, cons_append, nil_eq_append,
    and_false, not_false_eq_true, not_sym, false_and] at gu
  rename_i h t ind
  intro g; unfold is_first_substringcharIndex is_substringcharIndex at g
  obtain ⟨u1, u2, gu⟩ := g.left; have g:= g.right
  unfold substring_charIndex substring_charIndex_aux
  cases ss; simp only [Option.some.injEq]
  have : ∃ s0 s2, h :: t = s0 ++ [] ++ s2 ∧ s0.length = 0:= by
    use [], h::t; simp only [List.append_nil, List.nil_append, length_nil, and_self]
  have g:= g 0 this; omega
  rename_i hs1 ts1 _; simp only [zero_add]
  split; rename_i gx; have gx:= IsPrefix_isPrefixOf_EQ.mp gx; unfold List.IsPrefix at gx
  obtain ⟨t1, gx⟩ := gx ;
  have : ∃ s0 s2, h :: t = s0 ++ hs1 :: ts1 ++ s2 ∧ s0.length = 0 :=by
    use [], t1; simp only [List.nil_append, gx, length_nil, and_self]
  have g:= g 0 this; simp only [Option.some.injEq] ; omega
  have: is_first_substringcharIndex t (hs1 :: ts1) (i-1) := by
    unfold is_first_substringcharIndex is_substringcharIndex
    constructor
    cases u1; simp only [List.nil_append, cons_append, cons.injEq, length_nil] at gu
    have gc: List.IsPrefix (hs1 :: ts1) (h :: t) := by
      unfold List.IsPrefix; use u2; simp only [cons_append, gu]
    have gc:= IsPrefix_isPrefixOf_EQ.mpr gc; contradiction
    rename_i hu1 tu1; simp only [cons_append, List.append_assoc, cons.injEq, length_cons] at gu
    use tu1, u2; simp only [gu, List.append_assoc, cons_append, true_and]; omega
    intro i0 gi0; obtain ⟨v0, v2, gv⟩:=gi0
    have : ∃ s0 s2, h :: t = s0 ++ hs1 :: ts1 ++ s2 ∧ s0.length = i0 + 1 := by
      use h::v0, v2; simp only [gv, List.append_assoc, cons_append, length_cons, and_self]
    have g:= g (i0+1) this; omega
  have ind:= ind this; unfold substring_charIndex at ind
  have ind: substring_charIndex_aux t (hs1 :: ts1) (0+1) = some (i - 1 + 1 ):= sub_substring_charIndex_some_sound_mpr ind
  simp only [zero_add] at ind;
  have : i > 0 := by
    cases u1; simp only [List.nil_append, cons_append, cons.injEq, length_nil] at gu
    have gc: List.IsPrefix (hs1 :: ts1) (h :: t) := by
      unfold List.IsPrefix; use u2; simp only [cons_append, gu]
    have gc:= IsPrefix_isPrefixOf_EQ.mpr gc; contradiction
    simp only [cons_append, List.append_assoc, cons.injEq, length_cons] at gu; omega
  have : i = i - 1 + 1:= by omega
  rw[this, ind]

lemma substring_charIndex_of_nil: ss.length > 0 → substring_charIndex [] ss = none :=by
  intro g; unfold substring_charIndex substring_charIndex_aux
  cases ss; simp only [length_nil, gt_iff_lt, lt_self_iff_false] at g
  simp only

lemma exists_first_substring_charIndex: (∃ i, is_substringcharIndex s ss i) → ∃ i, is_first_substringcharIndex s ss i :=by
  unfold is_first_substringcharIndex; exact exists_minima_prop_nat

lemma substring_charIndex_aux_para1_sub (g: substring_charIndex_aux s ss i = some k) (gx: x ≤ i): substring_charIndex_aux s ss (i-x)= some (k-x) :=by
  induction s generalizing i x
  cases ss; unfold substring_charIndex_aux at g; simp only [Option.some.injEq] at g
  unfold substring_charIndex_aux;
  simp only [g, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  simp only [substring_charIndex_aux, not_false_eq_true, not_sym] at g
  rename_i h t ind
  cases ss; simp only [substring_charIndex_aux, Option.some.injEq] at g
  simp only [substring_charIndex, substring_charIndex_aux, g, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  rename_i h1 t1
  unfold substring_charIndex_aux at g; split at g; simp only [Option.some.injEq] at g
  rename_i g1; unfold substring_charIndex_aux;
  simp only [g1, ↓reduceIte, g, ge_iff_le, le_refl, tsub_eq_zero_of_le]
  have g: substring_charIndex_aux t (h1 :: t1) (i + 1 - x) = some (k - x) :=by apply ind g; linarith
  unfold substring_charIndex_aux; rename_i g1 _; simp only [add_tsub_cancel_left] at g
  simp only [g1, not_false_eq_true, not_sym, ↓reduceIte, zero_add]
  have : i + 1 - x = i - x + 1 :=by omega
  rw [← this, g]

lemma substring_charIndex_terminate (t: substring_charIndex s ss = some i) (h1: ss.length > 0 ): s.length - (i + ss.length) < s.length:= by
  induction s generalizing i;
  cases ss; simp only [length_nil, gt_iff_lt, lt_self_iff_false] at h1
  unfold substring_charIndex substring_charIndex_aux at t; simp only [Option.some.injEq] at t;
  cases ss; simp only [length_nil, gt_iff_lt, lt_self_iff_false] at h1
  unfold substring_charIndex substring_charIndex_aux at t; split at t
  rename_i h0; have h0:= prefix_length_le (IsPrefix_isPrefixOf_EQ.mp h0); simp only [Option.some.injEq] at t
  rw[← t]; simp only [length_cons, zero_add, succ_sub_succ_eq_sub, gt_iff_lt]
  simp only [length_cons] at h0; rename_i h v g1 t1 ind hx
  have:  v.length - t1.length ≤ v.length := by apply Nat.sub_le
  have: v.length < succ v.length :=by linarith
  linarith
  rename_i h v g1 t1 ind hx
  have e1: substring_charIndex_aux v (g1 :: t1) (0 + 1 -1) = some (i-1) :=by apply substring_charIndex_aux_para1_sub t; linarith
  simp only [zero_add, ge_iff_le, le_refl, tsub_eq_zero_of_le] at e1
  rw[← substring_charIndex] at e1; have _:= ind e1 ; simp only [length_cons, gt_iff_lt] ; omega

lemma not_contain_substring_until_substring_charIndex (gss: ss.length > 0) : substring_charIndex s ss = some i → ¬ contains_substring (List.take i s) ss = true := by
  intro g; have g:= substring_charIndex_some_sound.mp g
  rw[contains_substring_EQ]; unfold contains_substring_def
  unfold is_first_substringcharIndex at g
  by_contra; rename_i gc; obtain ⟨u1, u2, gc⟩ := gc
  unfold is_substringcharIndex at g
  have gr:= g.right ; have gl:=g.left
  obtain ⟨v1, v2, gv⟩ := gl
  have gr:= gr (u1.length)
  have: ∃ s0 s2, s = s0 ++ ss ++ s2 ∧ s0.length = u1.length :=by
    use u1, u2 ++ s.drop i
    have : s = s.take i ++ s.drop i :=by simp only [take_append_drop]
    rw(config:={occs:=.pos [1]})[this]; rw[gc]; simp only [List.append_assoc, and_self]
  have gr:= gr this
  have : length (List.take i s) = u1.length + ss.length + u2.length :=by
    simp only [gc, List.append_assoc, length_append]; linarith
  simp only [length_take] at this; omega

-- Returns list of char indexes of Chars in s satisfying char filter f
def list_char_filter_charIndex_aux (s: Str) (f: Char → Bool) (curpos : Nat) : List Nat :=  match s with
  | [] => []
  | h::t => if f h then curpos::list_char_filter_charIndex_aux t f (curpos + 1)
            else list_char_filter_charIndex_aux t f (curpos + 1)

def list_char_filter_charIndex (s: Str) (f: Char → Bool) := list_char_filter_charIndex_aux s f 0


lemma list_char_filter_charIndex_aux_ge: m ∈ list_char_filter_charIndex_aux s f k →  m ≥ k :=by
  induction s generalizing k
  unfold list_char_filter_charIndex_aux; simp only [not_mem_nil, ge_iff_le, IsEmpty.forall_iff, forall_const]
  rename_i h t ind
  simp only [list_char_filter_charIndex_aux, ge_iff_le]
  split; simp only [mem_cons, forall_eq_or_imp, le_refl, true_and]
  intro gm;  cases gm; omega; rename_i gm; have gm:= ind gm; omega
  intro gm; have gm:= ind gm; omega

lemma list_char_filter_charIndex_aux_nil: list_char_filter_charIndex_aux s f c = [] → ∀ m ∈ s, ¬ f m := by
  induction s generalizing c
  simp only [list_char_filter_charIndex_aux, not_mem_nil, Bool.not_eq_true, IsEmpty.forall_iff,
    forall_const, forall_true_left]
  rename_i h t ind
  simp only [list_char_filter_charIndex_aux, mem_cons, Bool.not_eq_true, forall_eq_or_imp]
  split; simp only [IsEmpty.forall_iff]; simp_all only [Bool.not_eq_true, true_and]; exact ind

lemma list_char_filter_charIndex_nil: list_char_filter_charIndex s f = [] → ∀ m ∈ s, ¬ f m := by
  unfold list_char_filter_charIndex; exact list_char_filter_charIndex_aux_nil

lemma list_char_filter_charIndex_aux_para1_add : list_char_filter_charIndex_aux s f (a+b) =  List.map (fun x=> x+a) (list_char_filter_charIndex_aux s f b) :=by
  induction s generalizing a b
  simp only [list_char_filter_charIndex_aux, map_nil]
  rename_i h t ind
  simp only [list_char_filter_charIndex_aux]
  have : a + b + 1 = a + (b + 1) := by omega
  split; simp only [map_cons, cons.injEq, true_and]; constructor; apply Nat.add_comm
  rw[this]; exact ind; rw[this]; exact ind

lemma list_char_filter_charIndex_aux_para1_elim : list_char_filter_charIndex s f =  List.map (fun x=> x-a) (list_char_filter_charIndex_aux s f a) :=by
  unfold list_char_filter_charIndex
  have: a = a + 0 :=by simp only [add_zero]
  rw(config:={occs:=.pos [2]})[this]; rw[list_char_filter_charIndex_aux_para1_add, map_add_sub]

lemma list_char_filter_charIndex_aux_para1_elim_mpr : list_char_filter_charIndex_aux s f a =  List.map (fun x=> x+a) (list_char_filter_charIndex s f)  :=by
  have:  list_char_filter_charIndex s f =  List.map (fun x=> x-a) (list_char_filter_charIndex_aux s f a) := list_char_filter_charIndex_aux_para1_elim
  rw[this, map_sub_add]; intro m gm; exact list_char_filter_charIndex_aux_ge gm

theorem list_char_filter_charIndex_sound : i ∈ list_char_filter_charIndex s f ↔ (∃ m, s.get? i = some m ∧ f m) :=by
  induction s generalizing i
  unfold list_char_filter_charIndex list_char_filter_charIndex_aux;
  simp only [not_mem_nil, get?_nil, not_false_eq_true, not_sym, false_and, exists_const]
  rename_i h t ind
  constructor
  simp only [list_char_filter_charIndex, list_char_filter_charIndex_aux, zero_add]
  intro gi; split at gi
  simp only [mem_cons] at gi ; cases gi; rename_i gi gf; simp only [gf, get?_cons_zero, Option.some.injEq, exists_eq_left', gi]
  rename_i gi; rw[list_char_filter_charIndex_aux_para1_elim_mpr] at gi
  simp only [mem_map] at gi; obtain ⟨a, ga⟩:= gi;
  have ind:= ind.mp ga.left; obtain ⟨m, gm⟩:=ind;
  use m; rw[← ga.right]; simp only [get?_cons_succ, gm, and_self]
  rw[list_char_filter_charIndex_aux_para1_elim_mpr] at gi
  simp only [mem_map] at gi; obtain ⟨a, ga⟩:= gi;
  have ind:= ind.mp ga.left; obtain ⟨m, gm⟩:=ind;
  use m; rw[← ga.right]; simp only [get?_cons_succ, gm, and_self]
  --mpr
  intro gm; obtain ⟨m, gm⟩:=gm;
  cases i; simp only [zero_eq, get?_cons_zero, Option.some.injEq] at gm
  unfold list_char_filter_charIndex list_char_filter_charIndex_aux; rw[gm.left, gm.right]
  simp only [zero_eq, ↓reduceIte, zero_add, mem_cons, true_or]
  rename_i n; simp only [get?_cons_succ] at gm
  have: ∃ m, List.get? t n = some m ∧ f m = true :=by use m
  have ind:= ind.mpr this
  unfold list_char_filter_charIndex list_char_filter_charIndex_aux;
  split ; simp only [zero_add, mem_cons, succ_ne_zero, not_false_eq_true, not_sym, false_or]
  rw[list_char_filter_charIndex_aux_para1_elim_mpr];
  simp only [mem_map, succ.injEq, exists_eq_right, ind]
  rw[list_char_filter_charIndex_aux_para1_elim_mpr];
  simp only [mem_map, succ.injEq, exists_eq_right, ind]


-- Returns list of char indexes of String ss in String s
def list_substring_charIndex_aux (s: Str) (ss: Str) (curpos : Nat) : List Nat :=
  if _h : ss.length > 0 then
    match _t: substring_charIndex s ss with
      | none => []
      | some i => (curpos + i) :: list_substring_charIndex_aux (s.drop (i + ss.length)) ss (curpos + i + ss.length)
  else list_nat_zero_to s.length
termination_by length s
decreasing_by simp_wf; have:= substring_charIndex_terminate _t _h; simp only [_h, or_true, and_true, gt_iff_lt]; omega

def list_substring_charIndex (s: Str) (ss: Str) := list_substring_charIndex_aux s ss 0

lemma list_substring_charIndex_aux_ge (gss: ss.length > 0) : v ∈ list_substring_charIndex_aux s ss k →  v ≥ k :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s k
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold list_substring_charIndex_aux;
  have: substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[this]; simp only [gt_iff_lt, gss, ↓reduceDIte, not_mem_nil, ge_iff_le, IsEmpty.forall_iff]
  unfold list_substring_charIndex_aux
  simp only [gt_iff_lt, gss, ↓reduceDIte, ge_iff_le]
  split; simp only [not_mem_nil, IsEmpty.forall_iff]
  rename_i i _; simp only [mem_cons]; intro gv
  cases gv; omega; rename_i gv
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by
    rw[← gm, ← gl] ; simp only [length_drop]; omega
  have ind:=ind m id1 gm gv ; omega

lemma list_substring_charIndex_aux_para1_add (gss: ss.length > 0)
      :list_substring_charIndex_aux s ss (a+b) =  List.map (fun x=> x+a) (list_substring_charIndex_aux s ss b) :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s a b
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold list_substring_charIndex_aux
  have: substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[this]; simp only [gt_iff_lt, gss, ↓reduceDIte, map_nil]
  unfold list_substring_charIndex_aux; simp only [gt_iff_lt, gss, ↓reduceDIte]
  split ; simp only [map_nil]; rename_i i _
  simp only [map_cons, cons.injEq]; constructor; omega
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by
    rw[← gm, ← gl] ; simp only [length_drop]; omega
  have : a + b + i + ss.length = a + (b + i + ss.length) := by omega
  rw[this]; exact ind m id1 gm

lemma list_substring_charIndex_aux_para1_elim (gss: ss.length > 0):
    list_substring_charIndex s ss =  List.map (fun x=> x-a) (list_substring_charIndex_aux s ss a) :=by
  unfold list_substring_charIndex
  have: a = a + 0 :=by simp only [add_zero]
  rw(config:={occs:=.pos [2]})[this]; rw[list_substring_charIndex_aux_para1_add gss, map_add_sub]

lemma list_substring_charIndex_aux_para1_elim_mpr (gss: ss.length > 0):
    list_substring_charIndex_aux s ss a =  List.map (fun x=> x + a) (list_substring_charIndex s ss) :=by
  have: list_substring_charIndex s ss =  List.map (fun x=> x-a) (list_substring_charIndex_aux s ss a) := list_substring_charIndex_aux_para1_elim gss
  rw[this, map_sub_add]; intro m gm; exact list_substring_charIndex_aux_ge gss gm

--Did not find a good way to state the mpr direction in a non recursive way
theorem list_substring_charIndex_sound (gss: ss.length >0): i ∈ list_substring_charIndex s ss →  List.IsPrefix ss (s.drop i)  :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s i
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold list_substring_charIndex list_substring_charIndex_aux
  have: substring_charIndex [] ss = none := substring_charIndex_of_nil gss; rw[this]
  simp only [gt_iff_lt, gss, ↓reduceDIte, not_mem_nil, drop_nil, prefix_nil, IsEmpty.forall_iff];
  unfold list_substring_charIndex list_substring_charIndex_aux
  simp only [gt_iff_lt, gss, ↓reduceDIte, zero_add]
  intro gi; split at gi; simp only [not_mem_nil] at gi;
  rename_i i0 gi0; rw[list_substring_charIndex_aux_para1_elim_mpr gss] at gi
  simp only [mem_cons, mem_map] at gi
  have gi0:= substring_charIndex_some_sound.mp gi0
  unfold is_first_substringcharIndex at gi0;
  have gi0:=gi0.left; unfold is_substringcharIndex at gi0; obtain ⟨s0,s2,gi0⟩:=gi0
  cases gi; rename_i gi; rw[gi];
  rw[gi0.left, ← gi0.right]; simp only [List.append_assoc, drop_left, prefix_append]
  generalize gm: (List.drop (i0 + ss.length) s).length = m
  have id1: m < n := by
    rw[← gm, ← gl] ; simp only [length_drop]; omega
  rename_i ga; obtain ⟨a, ga⟩:= ga
  have ind:=ind m id1 gm ga.left
  rw[gi0.left, ← gi0.right] at ind; simp only [List.append_assoc, drop_drop] at ind
  rw[← gi0.right] at ga; rw[ga.right] at ind
  have: s0 ++ (ss ++ s2) = s:= by simp only [gi0, List.append_assoc]
  rw[this] at ind ; exact ind

-- Similar to split_at but use char index instead of byte index (position)
def split_at_charIndex (s: Str) (i: Nat): List Char × List Char  := match s with
  | [] => ([], [])
  | h::t => if i = 0 then ([], s) else  let l := split_at_charIndex t (i-1)
            (h::(l.1), l.2)

def split_at_charIndex_def (s: Str) (i: Nat) := (s.take i, s.drop i)

theorem split_at_charIndex_EQ : split_at_charIndex s i = split_at_charIndex_def s i :=by
  induction s generalizing i; simp only [split_at_charIndex, split_at_charIndex_def, take_nil, drop_nil]
  rename_i h t ind
  simp only [split_at_charIndex, split_at_charIndex_def]
  split; rename_i gi; rw[gi]; simp only [zero_add, take_cons_succ, take_zero, drop_succ_cons,drop_zero]
  simp only [Prod.mk.injEq]; rw[ind]; unfold split_at_charIndex_def
  simp; cases i; contradiction;
  simp only [succ_sub_succ_eq_sub, tsub_zero, take_cons_succ, drop_succ_cons, and_self]

lemma split_at_charIndex_merge: (split_at_charIndex s i).1 ++ (split_at_charIndex s i).2 = s := by
  rw[split_at_charIndex_EQ, split_at_charIndex_def]; simp only [take_append_drop]

lemma split_at_charIndex_zero: split_at_charIndex s 0 = ([], s):=by
  unfold split_at_charIndex
  split; simp only; simp only [↓reduceIte]

def valid_split_charIndex_list (l: List Nat) (s: Str) := (monotone l) ∧ (∀ m ∈ l, m ≤ s.length)

def split_at_charIndex_list_aux (s: Str) (l: List Nat) (curpos: Nat): List Str := match l with
  | [] => [s]
  | h::t => (split_at_charIndex s (h - curpos)).1 :: split_at_charIndex_list_aux (split_at_charIndex s (h - curpos)).2 t h

--split a string s at char indexes in l
def split_at_charIndex_list (s: Str) (l: List Nat) (_ : valid_split_charIndex_list l s):= split_at_charIndex_list_aux s l 0

lemma split_at_charIndex_list_aux_para1_add :
      split_at_charIndex_list_aux s l c  = split_at_charIndex_list_aux s (List.map (fun x => x+a) l) (c+a):=by
  induction l generalizing s c a
  simp only [split_at_charIndex_list_aux]
  rename_i h t ind
  simp only [split_at_charIndex_list_aux, cons.injEq];
  have : h + a - (c + a) = h - c :=by omega
  rw[this]; constructor; simp only; exact ind

lemma split_at_charIndex_list_aux_para1_sub (g: ∀ m ∈ l, m ≥ a) (h: c ≥ a):
    split_at_charIndex_list_aux s l c  = split_at_charIndex_list_aux s (List.map (fun x => x - a) l) (c - a):=by
  have e1: split_at_charIndex_list_aux s (List.map (fun x => x - a) l) (c - a) =
          split_at_charIndex_list_aux s (List.map (fun x=> x+a) (List.map (fun x => x - a) l)) (c - a + a) := split_at_charIndex_list_aux_para1_add
  have e2: (List.map (fun x=> x+a) (List.map (fun x => x - a) l)) = l := map_sub_add g
  have e3: c - a + a = c:=by omega
  rw[e1,e2,e3]

lemma split_at_charIndex_list_aux_para1_elim (g: ∀ m ∈ l, m ≥ c) (gl: valid_split_charIndex_list (List.map (fun x => x - c) l) s):
  split_at_charIndex_list_aux s l c  = split_at_charIndex_list s (List.map (fun x => x - c) l) gl:=by
  unfold split_at_charIndex_list; rw[@split_at_charIndex_list_aux_para1_sub l c c s g];
  simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le]; simp only [ge_iff_le, le_refl]

lemma split_at_charIndex_list_aux_merge : flatten (split_at_charIndex_list_aux s l c) = s :=by
  unfold flatten
  induction l generalizing s c
  unfold split_at_charIndex_list_aux ;
  simp only [foldl_cons, append_eq, List.nil_append, foldl_nil]
  rename_i h t ind
  unfold split_at_charIndex_list_aux
  simp only [tsub_zero, foldl_cons, append_eq, List.nil_append]
  rw[fold_append_para1_elim, ind, split_at_charIndex_merge]

lemma split_at_charIndex_list_merge : flatten (split_at_charIndex_list s l g) = s :=by
  unfold split_at_charIndex_list; exact split_at_charIndex_list_aux_merge

-- Returns list of the distances between two consecutive char indexes in list l
-- Used in stating the soundness theorem of split_at_charIndex_list
def length_list_from_list_charIndex_aux (l: List Nat) (curpos: Nat):= match l with
  | [] => []
  | h::t => (h - curpos)::(length_list_from_list_charIndex_aux t h)

def length_list_from_list_charIndex (l: List Nat) (s: Str) := length_list_from_list_charIndex_aux (l++[s.length]) 0

lemma length_list_from_list_charIndex_aux_para1_elim (g0: monotone l) (g1:v ≥ k) (g2: ∀ m ∈ l, m ≥ k) (g3: ∀ m ∈ l, m ≤ v):
        length_list_from_list_charIndex_aux (List.map (fun x => x - k) l ++ [v - k]) 0 = length_list_from_list_charIndex_aux (l ++ [v]) k :=by
  generalize gll: l.length  = n
  induction n using Nat.strong_induction_on generalizing l v k
  rename_i n ind
  by_cases (n=0) ; rename_i gn; rw[gn] at gll ; have gll:= List.eq_nil_of_length_eq_zero gll; rw[gll]
  unfold length_list_from_list_charIndex_aux ;
  simp only [map_nil, List.nil_append, tsub_zero, cons.injEq, true_and]; unfold length_list_from_list_charIndex_aux ; simp only
  cases l ; simp only [length_nil] at gll; omega ; rename_i h t
  unfold length_list_from_list_charIndex_aux ;
  simp only [map_cons, cons_append, tsub_zero, cons.injEq, true_and]
  simp only [mem_cons, ge_iff_le, forall_eq_or_imp] at g2 g3
  unfold monotone at g0; simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq] at g0
  generalize gm: t.length = m
  have id1: m < n := by rw[← gm, ← gll]; simp only [length_map, length_cons, lt_succ_self]
  have id2: v  ≥  h  := by omega
  have id3: ∀ m ∈ t, m ≥ h  := by exact g0.left
  have id4: ∀ m ∈ t, m ≤ v  := by exact g3.right
  have id0: monotone t:= by exact g0.right
  have ind2:= ind m id1 id0 id2 id3 id4 gm
  generalize gm: (List.map (fun x => x - k) t).length = m
  have id1: m < n := by rw[← gm, ← gll]; simp only [length_map, length_cons, lt_succ_self]
  have id2: v - k ≥  h - k := by omega
  have id3: ∀ m ∈ (List.map (fun x => x - k) t), m ≥ h - k  := by
    intro m; simp only [mem_map, ge_iff_le, tsub_le_iff_right, forall_exists_index, and_imp]
    intro x gx1 gx2 ; have gx1:= id3 x gx1; omega
  have id4: ∀ m ∈ (List.map (fun x => x - k) t), m ≤ v - k  := by
    intro m; simp only [mem_map, forall_exists_index, and_imp]
    intro x gx1 gx2; have gx1:= id4 x gx1 ; omega
  have id0: monotone (List.map (fun x => x - k) t):= map_sub_monotone id0
  have ind1:= ind m id1 id0 id2 id3 id4 gm
  have : v - k - (h - k) = v - h := by omega
  rw[this] at ind1 ; simp only [map_map] at ind1
  have : (fun x => x - (h - k)) ∘ (fun x => x - k) = (fun x => x - h) :=by
    ext x; simp only [Function.comp_apply]; omega
  rw[this] at ind1 ;
  rw[← ind1, ← ind2]

theorem split_at_charIndex_list_sound : (sl = split_at_charIndex_list s l gl)
      ↔ (flatten sl = s) ∧ (List.map (fun x: Str => x.length) sl = length_list_from_list_charIndex l s) :=by
  generalize gll: l.length  = n
  induction n using Nat.strong_induction_on generalizing s l sl gl
  rename_i n ind
  by_cases (n=0) ; rename_i gn; rw[gn] at gll ; have gll:= List.eq_nil_of_length_eq_zero gll; simp only [gll]
  unfold split_at_charIndex_list  split_at_charIndex_list_aux length_list_from_list_charIndex flatten
  simp only [List.nil_append]; constructor; intro g; rw[g, length_list_from_list_charIndex_aux] ;
  simp only [foldl_cons, append_eq, List.nil_append, foldl_nil, map_cons, map_nil, tsub_zero, cons.injEq, true_and, length_list_from_list_charIndex_aux]
  simp only [length_list_from_list_charIndex_aux, tsub_zero, and_imp]; intro g g1
  unfold List.map at g1; split at g1; simp only [not_false_eq_true, not_sym] at g1
  rename_i h1 t1; simp only [cons.injEq, map_eq_nil, true_and] at g1; rw[g1.right]; rw[g1.right] at g
  simp only [foldl_cons, append_eq, List.nil_append, foldl_nil] at g; rw[g]
  cases l; simp only [length_nil] at gll; omega
  rename_i h t
  unfold valid_split_charIndex_list monotone at gl;
  simp only [Bool.decide_and, Bool.decide_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, mem_cons, forall_eq_or_imp] at gl
  have g1: h ≤ s.length := by simp only [gl]
  have g2: ∀ m ∈ t , m ≥ h := by exact gl.left.left
  have g3: ∀ m ∈ t , m ≤ s.length  :=by exact gl.right.right
  have _: valid_split_charIndex_list t s := by unfold valid_split_charIndex_list; simp only [gl,true_and]; exact g3
  have g4: valid_split_charIndex_list (List.map (fun x => x - h) t) (drop h s) :=by
    unfold valid_split_charIndex_list;
    constructor;
    apply map_sub_monotone gl.left.right;
    simp only [mem_map, length_drop, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, tsub_le_iff_right]
    intro a ga; have g3:= g3 a ga; omega
  constructor; intro g; rw[g, split_at_charIndex_list_merge]; simp only [cons_append, true_and]
  unfold split_at_charIndex_list split_at_charIndex_list_aux length_list_from_list_charIndex length_list_from_list_charIndex_aux
  simp only [tsub_zero, map_cons, cons_append, cons.injEq]
  rw[split_at_charIndex_EQ, split_at_charIndex_def]; simp only [length_take, min_eq_left_iff]
  constructor; exact g1;
  rw[split_at_charIndex_list_aux_para1_elim g2 g4]
  generalize gm: (List.map (fun x => x - h) t).length = m
  have id1: m < n:= by rw[← gll, ← gm]; simp only [length_map, length_cons, lt_succ_self]
  have id2: valid_split_charIndex_list (List.map (fun x => x - h) t) (List.drop h s) :=by
    unfold valid_split_charIndex_list; constructor; apply map_sub_monotone gl.left.right
    intro j; simp only [mem_map, length_drop, forall_exists_index, and_imp]
    intro x gx1 gx2; have gx1:= g3 x gx1; omega
  generalize gss: (split_at_charIndex_list (List.drop h s) (List.map (fun x => x - h) t)) id2 = ss; symm at gss
  have ind:= ((ind m id1 gm).mp gss).right
  rw[ind, length_list_from_list_charIndex]; simp only [length_drop]
  rw[length_list_from_list_charIndex_aux_para1_elim]
  exact gl.left.right; simp only [ge_iff_le, gl]; exact g2; exact g3
  --mpr
  intro g; unfold split_at_charIndex_list split_at_charIndex_list_aux
  rw[split_at_charIndex_EQ, split_at_charIndex_def]; simp only [tsub_zero]
  rw[split_at_charIndex_list_aux_para1_elim g2 g4]
  unfold length_list_from_list_charIndex length_list_from_list_charIndex_aux at g
  simp only [cons_append, tsub_zero] at g
  cases sl; simp only [map_nil, not_false_eq_true, not_sym, and_false] at g
  rename_i hsl tsl; simp only [flatten_cons, map_cons, cons.injEq] at g
  have: hsl = List.take h s :=by
    rw[← g.right.left]; symm; apply prefix_eq_take;
    unfold List.IsPrefix; use flatten tsl; simp only [g]
  simp only [this, cons.injEq, true_and]
  generalize gm: (List.map (fun x => x - h) t).length = m
  have id1: m < n:= by rw[← gll, ← gm]; simp only [length_map, length_cons, lt_succ_self]
  have id3: flatten tsl = (List.drop h s) := by
    have gd: s = (List.take h s) ++ (List.drop h s) :=by simp only [take_append_drop]
    have gl:= g.left; rw[gd, ← this] at gl;
    simp only [append_cancel_left_eq] at gl; exact gl
  have id4: List.map (fun x => x.length) tsl = length_list_from_list_charIndex (List.map (fun x => x - h) t) (List.drop h s) :=by
    rw[g.right.right]; unfold length_list_from_list_charIndex
    simp only [length_drop]
    rw[length_list_from_list_charIndex_aux_para1_elim]
    exact gl.left.right; simp only [ge_iff_le, gl]; exact g2; exact g3
  have id3: (flatten tsl = (List.drop h s)) ∧
        (List.map (fun x => x.length) tsl = length_list_from_list_charIndex (List.map (fun x => x - h) t) (List.drop h s)) :=by
    simp only [id3,id4, and_self]
  exact  (@ind m id1 tsl (List.drop h s) (map (fun x ↦ x - h) t) g4 gm).mpr id3

def list_char_filter_pos_aux (s: Str) (f: Char → Bool) (curpos : Nat) : List Nat :=  match s with
  | [] => []
  | h::t => if f h then curpos::list_char_filter_pos_aux t f (curpos + Char.utf8Size h)
            else list_char_filter_pos_aux t f (curpos + Char.utf8Size h)

--Returns list of byte indexes (positions) of Chars in s satisfying the char filter f
def list_char_filter_pos (s: Str) (f: Char → Bool) := list_char_filter_pos_aux s f 0

def list_char_filter_pos_def (s: Str) (f: Char → Bool):= List.map (charIndex_to_pos s) (list_char_filter_charIndex s f)

lemma list_char_filter_pos_aux_ge: m ∈ list_char_filter_pos_aux s f k →  m ≥ k :=by
  induction s generalizing k
  unfold list_char_filter_pos_aux; simp only [not_mem_nil, ge_iff_le, IsEmpty.forall_iff, forall_const]
  rename_i h t ind
  simp only [list_char_filter_pos_aux, ge_iff_le]
  split; simp only [mem_cons, forall_eq_or_imp, le_refl, true_and]
  intro gm;  cases gm; omega; rename_i gm; have gm:= ind gm; omega
  intro gm; have gm:= ind gm; omega

lemma list_char_filter_pos_aux_nil: list_char_filter_pos_aux s f c = [] → ∀ m ∈ s, ¬ f m := by
  induction s generalizing c
  simp only [list_char_filter_pos_aux, not_mem_nil, Bool.not_eq_true, IsEmpty.forall_iff,
    forall_const, forall_true_left]
  rename_i h t ind
  simp only [list_char_filter_pos_aux, mem_cons, Bool.not_eq_true, forall_eq_or_imp]
  split; simp only [IsEmpty.forall_iff]; simp_all only [Bool.not_eq_true, true_and]; exact ind

lemma list_char_filter_pos_nil: list_char_filter_pos s f = [] → ∀ m ∈ s, ¬ f m := by
  unfold list_char_filter_pos; exact list_char_filter_pos_aux_nil

lemma list_char_filter_pos_aux_para1_add : list_char_filter_pos_aux s f (a+b) =  List.map (fun x=> x+a) (list_char_filter_pos_aux s f b) :=by
  induction s generalizing a b
  simp only [list_char_filter_pos_aux, map_nil]
  rename_i h t ind
  simp only [list_char_filter_pos_aux]
  have : a + b + Char.utf8Size h = a + (b + Char.utf8Size h) := by omega
  split; simp only [map_cons, cons.injEq, true_and]; constructor; apply Nat.add_comm
  rw[this]; exact ind; rw[this]; exact ind

lemma list_char_filter_pos_aux_para1_elim : list_char_filter_pos s f =  List.map (fun x=> x-a) (list_char_filter_pos_aux s f a) :=by
  unfold list_char_filter_pos
  have: a = a + 0 :=by simp only [add_zero]
  rw(config:={occs:=.pos [2]})[this]; rw[list_char_filter_pos_aux_para1_add, map_add_sub]

lemma list_char_filter_pos_aux_para1_elim_mpr : list_char_filter_pos_aux s f a =  List.map (fun x=> x+a) (list_char_filter_pos s f)  :=by
  have:  list_char_filter_pos s f =  List.map (fun x=> x-a) (list_char_filter_pos_aux s f a) := list_char_filter_pos_aux_para1_elim
  rw[this, map_sub_add]; intro m gm; exact list_char_filter_pos_aux_ge gm

theorem list_char_filter_pos_EQ: list_char_filter_pos s f = list_char_filter_pos_def s f :=by
  induction s
  simp only [list_char_filter_pos, list_char_filter_pos_aux, list_char_filter_pos_def,
    charIndex_to_pos, ite_self, list_char_filter_charIndex, list_char_filter_charIndex_aux, map_nil]
  rename_i h t ind
  simp only [list_char_filter_pos, list_char_filter_pos_aux, zero_add, list_char_filter_pos_def,
    list_char_filter_charIndex, list_char_filter_charIndex_aux]
  split
  simp only [map_cons, ↓reduceIte, cons.injEq, true_and]
  rw[list_char_filter_pos_aux_para1_elim_mpr, list_char_filter_charIndex_aux_para1_elim_mpr, ind, list_char_filter_pos_def]
  constructor; simp only [charIndex_to_pos, ↓reduceIte]
  simp only [map_map, map_inj_left, Function.comp_apply]
  intro m _;
  simp only [charIndex_to_pos, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, not_sym,
    ↓reduceIte, add_tsub_cancel_right, add_comm]
  rw[list_char_filter_pos_aux_para1_elim_mpr, list_char_filter_charIndex_aux_para1_elim_mpr, ind, list_char_filter_pos_def]
  simp only [map_map, map_inj_left, Function.comp_apply]
  intro m _;
  simp only [add_comm, charIndex_to_pos, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    not_sym, ↓reduceIte, add_tsub_cancel_right]

def list_substring_pos_aux (s: Str) (ss: Str) (curpos : Nat) : List Nat :=
  if _h : ss.length > 0 then
    match _t: substring_charIndex s ss with
      | none => []
      | some i => (curpos + (charIndex_to_pos s i)) :: list_substring_pos_aux (s.drop (i + ss.length)) ss (curpos + (charIndex_to_pos s i) + (byteSize ss))
  else list_nat_zero_to s.length
termination_by length s
decreasing_by simp_wf; have:= substring_charIndex_terminate _t _h; simp only [_h, or_true, and_true, gt_iff_lt, this]; omega

--Returns list of byte indexes (positions) of ss in s
def list_substring_pos (s: Str) (ss: Str) := list_substring_pos_aux s ss 0

def list_substring_pos_def (s: Str) (ss: Str):= List.map (charIndex_to_pos s) (list_substring_charIndex s ss)

lemma list_substring_pos_aux_ge (gss: ss.length > 0) : v ∈ list_substring_pos_aux s ss k →  v ≥ k :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s k
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold list_substring_pos_aux;
  have: substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[this]; simp only [gt_iff_lt, gss, ↓reduceDIte, not_mem_nil, ge_iff_le, IsEmpty.forall_iff]
  unfold list_substring_pos_aux
  simp only [gt_iff_lt, gss, ↓reduceDIte, ge_iff_le]
  split; simp only [not_mem_nil, IsEmpty.forall_iff]
  rename_i i _; simp only [mem_cons]; intro gv
  cases gv; omega; rename_i gv
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by
    rw[← gm, ← gl] ; simp only [length_drop]; omega
  have ind:=ind m id1 gm gv ; omega

lemma list_substring_pos_aux_para1_add (gss: ss.length > 0)
      :list_substring_pos_aux s ss (a+b) =  List.map (fun x=> x+a) (list_substring_pos_aux s ss b) :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s a b
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold list_substring_pos_aux
  have: substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[this]; simp only [gt_iff_lt, gss, ↓reduceDIte, map_nil]
  unfold list_substring_pos_aux; simp only [gt_iff_lt, gss, ↓reduceDIte]
  split ; simp only [map_nil]; rename_i i _
  simp only [map_cons, cons.injEq]; constructor; omega
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by rw[← gm, ← gl] ; simp only [length_drop]; omega
  have : a + b + charIndex_to_pos s i + byteSize ss = a + (b + charIndex_to_pos s i + byteSize ss) := by omega
  rw[this]; exact ind m id1 gm

lemma list_substring_pos_aux_para1_elim (gss: ss.length > 0):
    list_substring_pos s ss =  List.map (fun x=> x-a) (list_substring_pos_aux s ss a) :=by
  unfold list_substring_pos
  have: a = a + 0 :=by simp only [add_zero]
  rw(config:={occs:=.pos [2]})[this]; rw[list_substring_pos_aux_para1_add gss, map_add_sub]

lemma list_substring_pos_aux_para1_elim_mpr (gss: ss.length > 0):
    list_substring_pos_aux s ss a =  List.map (fun x=> x + a) (list_substring_pos s ss) :=by
  have: list_substring_pos s ss =  List.map (fun x=> x-a) (list_substring_pos_aux s ss a) := list_substring_pos_aux_para1_elim gss
  rw[this, map_sub_add]; intro m gm; exact list_substring_pos_aux_ge gss gm

theorem list_substring_pos_EQ (gss: ss.length>0): list_substring_pos s ss = list_substring_pos_def s ss :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold list_substring_pos list_substring_pos_aux list_substring_pos_def list_substring_charIndex list_substring_charIndex_aux
  have i1: substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[i1]; simp only [gt_iff_lt, gss, ↓reduceDIte, charIndex_to_pos, ite_self, map_nil]
  unfold list_substring_pos list_substring_pos_aux list_substring_pos_def list_substring_charIndex list_substring_charIndex_aux
  simp only [gt_iff_lt, gss, ↓reduceDIte, zero_add]
  split; simp only [map_nil]
  rename_i i gi;  simp only [map_cons, cons.injEq, true_and]
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by rw[← gm, ← gl] ; simp only [length_drop]; omega
  have ind:= ind m id1 gm
  rw[list_substring_pos_aux_para1_elim_mpr gss, list_substring_charIndex_aux_para1_elim_mpr gss, ind, list_substring_pos_def]
  simp only [map_map, map_inj_left, Function.comp_apply]
  intro m _ ; simp only [charIndex_to_pos_EQ, charIndex_to_pos_def]
  have: (take i s) ++ ss ++(take m (drop (i + length ss) s)) = take (m + (i + length ss)) s := by
    have: m + (i + length ss) = (i + length ss) + m := by omega
    rw[this, List.take_add, List.append_cancel_right_eq];
    have gi:= substring_charIndex_some_sound.mp gi
    unfold is_first_substringcharIndex at gi; have gi:=gi.left; unfold is_substringcharIndex at gi
    obtain⟨s0, s2, gi⟩:=gi
    have i1: take i s = s0 := by rw[← gi.right]; apply prefix_eq_take; simp only [gi.left, append_assoc, prefix_append]
    have i2: i + length ss = (s0 ++ ss).length:= by simp only [length_append, gi.right]
    have i2: take (i + length ss) s = s0 ++ ss := by rw[i2]; apply prefix_eq_take; rw[gi.left, List.IsPrefix]; use s2
    rw[i1,i2]
  rw[← this]; simp only [append_assoc, byteSize_concat]; omega



--#eval list_substring_charIndex "abcccabccddab".data "ab".data

/-
Function: split_inclusive
From: str::core::split_inclusive
Description: https://doc.rust-lang.org/std/primitive.str.html#method.split_inclusive
-/


def split_inclusive_char_filter_aux (s: Str) (f: Char → Bool) (w: Str) := match s with
  | [] => [w]
  | h::t => if f h then (w++[h])::split_inclusive_char_filter_aux t f []
            else split_inclusive_char_filter_aux t f (w++[h])

def split_inclusive_char_filter (s: Str) (f: Char → Bool) := split_inclusive_char_filter_aux s f []

lemma split_inclusive_char_filter_def_valid: valid_split_charIndex_list (List.map (fun x => x+1) (list_char_filter_charIndex s f)) s :=by
  induction s
  simp only [valid_split_charIndex_list, monotone, list_char_filter_charIndex,
    list_char_filter_charIndex_aux, map_nil, not_mem_nil, length_nil, nonpos_iff_eq_zero,
    false_implies, implies_true, and_self]
  rename_i h t ind
  unfold valid_split_charIndex_list at ind
  simp only [list_char_filter_charIndex, list_char_filter_charIndex_aux, zero_add]
  split
  simp only [valid_split_charIndex_list, monotone, mem_map, zero_add, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, le_add_iff_nonneg_left, _root_.zero_le, implies_true, true_and,
    Bool.decide_eq_true, map_cons, mem_cons, length_cons, forall_eq_or_imp, add_le_add_iff_right]
  rw[list_char_filter_charIndex_aux_para1_elim_mpr]
  constructor; exact map_add_monotone ind.left; exact ind.right
  rw[list_char_filter_charIndex_aux_para1_elim_mpr]
  unfold valid_split_charIndex_list
  constructor; exact map_add_monotone ind.left;
  simp only [map_map, comp_add_right, reduceAdd, mem_map, length_cons, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, reduceLeDiff]
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at ind
  exact ind.right

def split_inclusive_char_filter_def (s: Str) (f: Char → Bool):=
    split_at_charIndex_list s (List.map (fun x => x+1) (list_char_filter_charIndex s f)) split_inclusive_char_filter_def_valid

--#eval split_inclusive_char_filter_def "abbfsdhaasadsf".data (fun x => x ='a')

lemma split_inclusive_char_filter_aux_para1_append:
      split_inclusive_char_filter_aux s f v = hl::tl → split_inclusive_char_filter_aux s f (w++v) = (w ++ hl)::tl := by
  induction s generalizing w v
  simp only [split_inclusive_char_filter_aux, cons.injEq, and_imp]
  intro g1 g2 ; rw[← g1, g2]; simp only [List.append_nil, and_self]
  rename_i h t ind
  simp only [split_inclusive_char_filter_aux, List.nil_append]
  split; simp only [cons.injEq, append_cancel_left_eq, imp_self];
  intro g ; rw[← g.left]; simp only [List.append_assoc, g, and_self]
  have : w ++ v ++ [h] = w ++ (v ++ [h]) := by simp only [List.append_assoc]
  rw[this]; exact ind

lemma split_inclusive_char_filter_to_aux:
      split_inclusive_char_filter s f = hl::tl → split_inclusive_char_filter_aux s f w = (w ++ hl)::tl := by
  unfold split_inclusive_char_filter
  have : w = w ++ [] := by simp only [List.append_nil]
  rw(config:={occs:=.pos [1]})[this]; exact split_inclusive_char_filter_aux_para1_append

lemma flatten_split_inclusive_char_filter_aux_cons:
      List.foldl List.append [] (split_inclusive_char_filter_aux s f (v::u)) = v::(List.foldl List.append [] (split_inclusive_char_filter_aux s f u)) :=by
  induction s generalizing v u;
  simp only [split_inclusive_char_filter_aux, List.nil_append, foldl_cons, append_eq, foldl_nil, List.append_nil]
  rename_i h t ind
  simp only [split_inclusive_char_filter_aux, List.nil_append, singleton_append]
  split;
  simp only [singleton_append, foldl_cons, append_eq, List.nil_append, List.append_nil]
  have: v :: u ++ [h] = v :: (u ++ [h]) :=by simp only [cons_append]
  rw[this,fold_append_cons]; simp only [cons_append, ind]


lemma split_inclusive_char_filter_aux_para1_eq_length:  (split_inclusive_char_filter_aux s f w).length =  (split_inclusive_char_filter_aux s f u).length :=by
  induction s generalizing w u
  simp only [split_inclusive_char_filter_aux, length_append, List.length_singleton]
  rename_i h t ind
  unfold split_inclusive_char_filter_aux; split;
  simp only [List.append_assoc, singleton_append, length_append, length_cons]
  exact ind

lemma split_inclusive_char_filter_ne_nil : split_inclusive_char_filter s f ≠ [] :=by
  induction s
  simp only [split_inclusive_char_filter, split_inclusive_char_filter_aux, List.nil_append, ne_eq, not_false_eq_true, not_sym]
  rw [split_inclusive_char_filter, split_inclusive_char_filter_aux]; split
  simp only [List.nil_append, singleton_append, ne_eq,
    not_false_eq_true, not_sym]
  rename_i h t ind _
  have : (split_inclusive_char_filter_aux t f ([] ++ [h])).length = (split_inclusive_char_filter t f).length:= by
    unfold split_inclusive_char_filter; exact split_inclusive_char_filter_aux_para1_eq_length
  by_contra; rename_i gc; rw[gc] at this; simp only [length_nil] at this; symm at this
  have := List.eq_nil_of_length_eq_zero this; rw[this] at ind; contradiction

lemma split_inclusive_char_filter_aux_ne_nil : split_inclusive_char_filter_aux s f w ≠ [] :=by
  have i1: (split_inclusive_char_filter_aux s f w).length = (split_inclusive_char_filter_aux s f []).length := split_inclusive_char_filter_aux_para1_eq_length
  rw[← split_inclusive_char_filter] at i1
  by_contra; rename_i g; simp only [g, length_nil] at i1; symm at i1
  have i1:= List.eq_nil_of_length_eq_zero i1;
  simp only [length_nil,split_inclusive_char_filter_ne_nil, not_false_eq_true, not_sym] at i1


lemma split_inclusive_char_filter_aux_singleton_of_no_char_filter_charIndex :
    (∀ m ∈ s, ¬ f m) → split_inclusive_char_filter_aux s f w = [w++s] :=by
  induction s generalizing w;
  unfold  split_inclusive_char_filter_aux;
  simp only [not_mem_nil, Bool.not_eq_true, IsEmpty.forall_iff, forall_const, List.append_nil,forall_true_left]
  rename_i h t ind
  simp only [mem_cons, Bool.not_eq_true, forall_eq_or_imp, and_imp]
  intro g1 g2; simp only [split_inclusive_char_filter, split_inclusive_char_filter_aux, g1,
    not_false_eq_true, not_sym, ↓reduceIte, List.nil_append]
  have : w ++ h :: t = (w++[h]) ++ t :=by simp only [List.append_assoc, singleton_append]
  rw[this]; simp only [Bool.not_eq_true] at ind; exact ind g2

lemma split_inclusive_char_filter_singleton_of_no_char_filter_charIndex :
    (∀ m ∈ s, ¬ f m) → split_inclusive_char_filter s f = [s] :=by
  unfold split_inclusive_char_filter;
  have : s = [] ++ s := by simp only [List.nil_append]
  rw[this]; exact split_inclusive_char_filter_aux_singleton_of_no_char_filter_charIndex

lemma split_inclusive_char_filter_singleton_of_nil_list_char_filter_charIndex :
    list_char_filter_charIndex s f = [] → split_inclusive_char_filter s f  = [s] :=by
  intro g; exact split_inclusive_char_filter_singleton_of_no_char_filter_charIndex (list_char_filter_charIndex_nil g)


lemma split_inclusive_char_filter_def_aux_para1_elim :
      split_inclusive_char_filter_def s f = split_at_charIndex_list_aux s (List.map (fun x=> x+1) (list_char_filter_charIndex_aux s f c)) c :=by
  unfold split_inclusive_char_filter_def split_at_charIndex_list;
  have e1: split_at_charIndex_list_aux s (List.map (fun x => x + 1) (list_char_filter_charIndex s f)) 0 =
        split_at_charIndex_list_aux s (List.map (fun x => x +c) (List.map (fun x => x + 1) (list_char_filter_charIndex s f))) (0+c):= split_at_charIndex_list_aux_para1_add
  have e2: list_char_filter_charIndex s f = (List.map (fun x => x - c) (list_char_filter_charIndex_aux s f c)) := list_char_filter_charIndex_aux_para1_elim
  have e3: (List.map (fun x => x + c) (List.map (fun x => x + 1) (List.map (fun x => x - c) (list_char_filter_charIndex_aux s f c))))
            = List.map (fun x => x + 1) (list_char_filter_charIndex_aux s f c) := by
    rw[map_add_comm, map_sub_add]; intro m gm; apply list_char_filter_charIndex_aux_ge gm
  rw[e1, e2, e3]; simp only [zero_add]


theorem split_inclusive_char_filter_EQ: split_inclusive_char_filter s f = split_inclusive_char_filter_def s f :=by
  induction s ;
  unfold split_inclusive_char_filter split_inclusive_char_filter_def list_char_filter_charIndex
  unfold split_inclusive_char_filter_aux list_char_filter_charIndex_aux split_at_charIndex_list split_at_charIndex_list_aux
  simp only [map_nil]
  rename_i h t ind
  unfold split_inclusive_char_filter split_inclusive_char_filter_aux
  split; rename_i gf ; simp only [List.nil_append, zero_add, tsub_zero]
  unfold split_inclusive_char_filter_def list_char_filter_charIndex list_char_filter_charIndex_aux
  simp only [gf, ↓reduceIte, zero_add, List.nil_append]
  rw[split_at_charIndex_list]
  unfold split_at_charIndex_list_aux
  simp only [map_cons, zero_add, split_at_charIndex, tsub_zero, one_ne_zero, not_false_eq_true,
    not_sym, ↓reduceIte, ge_iff_le, le_refl, tsub_eq_zero_of_le, reduceAdd, cons.injEq, true_and]
  rw[← split_inclusive_char_filter, ind, split_at_charIndex_EQ, split_at_charIndex_def];
  simp only [take_zero, drop_zero, true_and]
  exact split_inclusive_char_filter_def_aux_para1_elim
  simp only [List.nil_append, split_inclusive_char_filter_def, list_char_filter_charIndex, list_char_filter_charIndex_aux]
  rename_i gf; simp only [gf, not_false_eq_true, not_sym, ↓reduceIte, zero_add];
  unfold split_at_charIndex_list split_at_charIndex_list_aux
  split; rename_i gc; simp only [map_eq_nil] at gc
  have gc:= list_char_filter_charIndex_aux_nil gc
  have gc: split_inclusive_char_filter t f = [t]:= split_inclusive_char_filter_singleton_of_no_char_filter_charIndex gc
  exact split_inclusive_char_filter_to_aux gc
  rename_i hlp tlp glp;
  have gsd: split_inclusive_char_filter_def t f
      = split_at_charIndex_list_aux t (List.map (fun x => x + 1)  (list_char_filter_charIndex_aux t f 1)) 1
            :=split_inclusive_char_filter_def_aux_para1_elim
  rw[glp, split_at_charIndex_list_aux, ← ind] at gsd
  have gsp: split_inclusive_char_filter_aux t f [h]
    = ([h] ++ (split_at_charIndex t (hlp - 1)).1 ):: split_at_charIndex_list_aux (split_at_charIndex t (hlp - 1)).2 tlp hlp
      := split_inclusive_char_filter_to_aux gsd
  rw[gsp]
  have i1: hlp -1 ≥ 1 := by
    have : list_char_filter_charIndex_aux t f 1 = List.map (fun x => x - 1) (hlp :: tlp):= by
      rw[← glp, map_add_sub]
    simp only [map_cons] at this
    have : hlp - 1 ∈ list_char_filter_charIndex_aux t f 1 :=by simp only [this, mem_cons, true_or]
    apply list_char_filter_charIndex_aux_ge this
  have i0: ¬ hlp = 0 :=by omega
  simp only [singleton_append, split_at_charIndex, tsub_zero, i0, not_false_eq_true, not_sym, ↓reduceIte]

lemma split_inclusive_char_filter_append_length: flatten (split_inclusive_char_filter s f) = s
      ∧ ((split_inclusive_char_filter s f).length = (List.filter f s).length + 1) :=by
  unfold flatten
  induction s
  simp only [split_inclusive_char_filter, split_inclusive_char_filter_aux, List.nil_append, foldl_cons, append_eq,
    List.append_nil, foldl_nil, filter_nil, List.length_singleton, length_nil, zero_add, and_self]
  rename_i h t ind
  constructor
  simp only [split_inclusive_char_filter, split_inclusive_char_filter_aux, List.nil_append]
  split; rw[ ← split_inclusive_char_filter]
  simp only [singleton_append, foldl_cons, append_eq, List.nil_append, fold_append_cons, ind]
  rw[flatten_split_inclusive_char_filter_aux_cons]; rw[← split_inclusive_char_filter, ind.left]
  --length
  simp only [split_inclusive_char_filter, split_inclusive_char_filter_aux, filter];
  split; rename_i gf; simp only [List.nil_append, gf, length_cons]
  rw[ ← split_inclusive_char_filter]
  simp only [singleton_append, length_cons, ind.right]
  rename_i gf; simp only [List.nil_append, gf, length_cons]
  have : (split_inclusive_char_filter_aux t f [h] ).length  = (split_inclusive_char_filter_aux t f [] ).length:= by
    apply split_inclusive_char_filter_aux_para1_eq_length
  rw[this, ← split_inclusive_char_filter, ind.right]

lemma split_inclusive_char_filter_merge: flatten (split_inclusive_char_filter s f) =  s :=by
  exact (@split_inclusive_char_filter_append_length s f).left

lemma split_inclusive_char_filter_singleton_of_length:
      (split_inclusive_char_filter s f).length = 1 → split_inclusive_char_filter s f = [s]:=by
  generalize g: (split_inclusive_char_filter s f) = si
  cases si;
  simp only [length_nil, zero_ne_one, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ; cases t; intro _;
  have : flatten (split_inclusive_char_filter s f) = flatten [h] := by rw[g]
  rw[split_inclusive_char_filter_merge, flatten] at this;
  simp only [foldl_cons, append_eq,List.nil_append, foldl_nil] at this
  rw[this];
  simp only [length_cons, succ.injEq, add_eq_zero, and_false, not_false_eq_true, not_sym,
    cons.injEq, IsEmpty.forall_iff]

lemma split_inclusive_char_filter_aux_flatten:
      flatten (split_inclusive_char_filter_aux s f w) = w ++ flatten (split_inclusive_char_filter s f) :=by
  induction s generalizing w
  unfold split_inclusive_char_filter split_inclusive_char_filter_aux flatten
  simp only [foldl_cons, append_eq, List.nil_append, foldl_nil, List.append_nil]
  rename_i h t ind
  unfold split_inclusive_char_filter split_inclusive_char_filter_aux flatten
  split; simp only [foldl_cons, append_eq, List.nil_append]
  rw[fold_append_para1_elim]; rw(config:={occs:=.pos [2]}) [fold_append_para1_elim]
  simp only [List.append_assoc, singleton_append]
  simp only [List.nil_append]; rw[← flatten, @ind (w++[h]), ← flatten, @ind [h]]
  simp only [List.append_assoc, singleton_append]


def split_inclusive_substring (s: Str) (ss: Str)  : List Str:=
  if h: ss.length > 0 then
    match _t: substring_charIndex s ss with
      | none =>  [s]
      | some i => (s.take (i + ss.length)) :: split_inclusive_substring (s.drop (i + ss.length)) ss
  else [[]] ++ List.map (fun c => [c]) s
termination_by length s
decreasing_by simp_wf; have:= substring_charIndex_terminate _t h; simp only [h, or_true, and_true, gt_iff_lt]; omega

lemma split_inclusive_substring_def_valid: valid_split_charIndex_list (List.map (fun x => x + ss.length) (list_substring_charIndex s ss)) s :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i n ind
  unfold valid_split_charIndex_list at *
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold list_substring_charIndex list_substring_charIndex_aux
  split; rename_i gss;
  have gk:= @substring_charIndex_of_nil ss gss; rw[gk];
  simp only [valid_split_charIndex_list, monotone,
    map_nil, not_mem_nil, length_nil, nonpos_iff_eq_zero, false_implies, implies_true, and_self]
  simp only [valid_split_charIndex_list, monotone, list_nat_zero_to, list_nat_zero_to_aux, map_nil, not_mem_nil,
    length_nil, nonpos_iff_eq_zero, false_implies, implies_true, and_self]
  unfold list_substring_charIndex list_substring_charIndex_aux
  split; split
  simp only [monotone, map_nil, not_mem_nil, false_implies, implies_true, and_self]
  rename_i i gi; simp only [monotone, zero_add, mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, add_le_add_iff_right, Bool.decide_and, Bool.decide_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, map_cons, mem_cons, forall_eq_or_imp]
  rw[list_substring_charIndex_aux_para1_elim_mpr (by assumption)]
  generalize gm: (drop (i + length ss) s).length = m
  have id1: m < n :=by rw[← gm, ← gl]; simp only [length_drop, tsub_lt_self_iff, add_pos_iff]; omega
  have ind:= ind m id1 gm
  constructor; constructor
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a _; omega
  have gk:= @map_add_monotone _ i ind.left; simp only [map_map, comp_add_right] at gk
  have : (fun x ↦ x + (length ss + i)) = (fun x ↦ x + (i + length ss)) :=by ext x; omega
  rw[this] at gk
  apply map_add_monotone gk
  constructor
  have: i + length ss ≤ length s := by
    have gi:= (substring_charIndex_some_sound.mp gi).left
    unfold is_substringcharIndex at gi; obtain⟨s0, s2, gi⟩:= gi
    have: s.length = s0.length + (ss.length + s2.length):= by simp only [gi.left, append_assoc, length_append]
    omega
  assumption
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [mem_map, length_drop, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at ind
  intro a ga; have g1:= ind.right a ga; omega
  constructor
  apply map_add_monotone; exact list_nat_zero_to_monotone
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  have : length ss = 0 := by omega
  simp only [this, add_zero]; exact list_nat_zero_to_le


def split_inclusive_substring_def (s: Str) (ss: Str):=
  split_at_charIndex_list s (List.map (fun x => x + ss.length) (list_substring_charIndex s ss)) split_inclusive_substring_def_valid

lemma split_inclusive_substring_ne_nil : split_inclusive_substring s ss ≠ [] :=by
  by_cases (ss.length > 0); rename_i gss
  unfold split_inclusive_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte, List.nil_append, ne_eq]
  split; simp only [not_false_eq_true, not_sym]
  simp only [singleton_append, not_false_eq_true, not_sym]
  have g: ss.length = 0 :=by omega
  have g:= eq_nil_of_length_eq_zero g
  simp only [g, split_inclusive_substring, length_nil, gt_iff_lt, lt_self_iff_false, ↓reduceDIte,
    singleton_append, ne_eq, not_false_eq_true, not_sym]


lemma list_substring_charIndex_aux_nil_of_substring_charIndex_none (gss: ss.length > 0):
    substring_charIndex s ss = none → list_substring_charIndex_aux s ss c = [] :=by
  unfold list_substring_charIndex_aux; intro g; rw[g]
  simp only [gt_iff_lt, gss, ↓reduceDIte]

lemma list_substring_charIndex_nil_of_substring_charIndex_none (gss: ss.length > 0):
    substring_charIndex s ss = none → list_substring_charIndex s ss = [] :=by
  unfold list_substring_charIndex; apply list_substring_charIndex_aux_nil_of_substring_charIndex_none gss

lemma split_inclusive_substring_def_singleton_of_substring_charIndex_none (gss: ss.length > 0):
    substring_charIndex s ss = none →  split_inclusive_substring_def s ss = [s] :=by
  intro g; have g:= list_substring_charIndex_nil_of_substring_charIndex_none gss g
  unfold split_inclusive_substring_def; simp only [g, map_nil]; unfold split_at_charIndex_list
  simp only [split_at_charIndex_list_aux]

lemma split_inclusive_substring_def_aux_para1_elim (gss: ss.length>0):
      split_inclusive_substring_def s ss = split_at_charIndex_list_aux s (List.map (fun x=> x + ss.length) (list_substring_charIndex_aux s ss c)) c :=by
  unfold split_inclusive_substring_def split_at_charIndex_list;
  have e1: split_at_charIndex_list_aux s (List.map (fun x => x + ss.length) (list_substring_charIndex s ss)) 0 =
        split_at_charIndex_list_aux s (List.map (fun x => x +c) (List.map (fun x => x + ss.length) (list_substring_charIndex s ss))) (0+c):= split_at_charIndex_list_aux_para1_add
  have e2: list_substring_charIndex s ss = (List.map (fun x => x - c) (list_substring_charIndex_aux s ss c)) := list_substring_charIndex_aux_para1_elim gss
  have e3: (List.map (fun x => x + c) (List.map (fun x => x + ss.length) (List.map (fun x => x - c) (list_substring_charIndex_aux s ss c))))
            = List.map (fun x => x + ss.length) (list_substring_charIndex_aux s ss c) := by
    rw[map_add_comm, map_sub_add]; intro m gm; apply list_substring_charIndex_aux_ge gss gm
  rw[e1, e2, e3]; simp only [zero_add]



lemma split_inclusive_substring_EQ_ss_nil: split_inclusive_substring s [] = split_inclusive_substring_def s [] :=by
  simp only [split_inclusive_substring, length_nil, gt_iff_lt, lt_self_iff_false, ↓reduceDIte,
    singleton_append, cons_append, split_inclusive_substring_def, add_zero, list_substring_charIndex,
    list_substring_charIndex_aux, map_id']
  simp only [nil_append, list_nat_zero_to]
  induction s
  simp only [map_nil, nil_append, split_at_charIndex_list, split_at_charIndex_list_aux, cons_ne_self,
    not_false_eq_true, not_sym]
  rename_i h t ind
  simp only [map_cons, split_at_charIndex_list, split_at_charIndex_list_aux, split_at_charIndex, le_refl,
    tsub_eq_zero_of_le, ↓reduceIte, zero_add, cons.injEq, true_and]
  unfold split_at_charIndex_list_aux
  split; rename_i gln;
  simp only [split_at_charIndex_list, @list_nat_zero_to_aux_para1_sub _ 0 1,
    zero_add, gln, map_nil, split_at_charIndex_list_aux, cons.injEq, map_eq_nil] at ind
  simp only [ind.right, map_nil]
  rename_i hl tl gln
  have ghl:= list_nat_zero_to_aux_first_mem gln; rw[ghl]
  simp only [split_at_charIndex, tsub_zero, one_ne_zero, not_false_eq_true, not_sym, ↓reduceIte,
    le_refl, tsub_eq_zero_of_le, cons.injEq, true_and]
  have: split_at_charIndex t 0 = ([],t) := split_at_charIndex_zero
  simp only [this, true_and];
  rw[@split_at_charIndex_list_aux_para1_sub _  1 1 _]; simp only [le_refl, tsub_eq_zero_of_le]
  unfold split_at_charIndex_list at ind
  simp only [@list_nat_zero_to_aux_para1_sub _ 0 1, zero_add, gln, ghl, map_cons, le_refl,
    tsub_eq_zero_of_le, split_at_charIndex_list_aux, this, cons.injEq, true_and] at ind; exact ind
  intro m gm
  have g:=@list_nat_zero_to_aux_ge m t.length 1;
  simp only [gln, ghl, mem_cons, gm, or_true, ge_iff_le,true_implies] at g
  omega; omega


theorem split_inclusive_substring_EQ : split_inclusive_substring s ss = split_inclusive_substring_def s ss :=by
  by_cases (ss.length = 0)
  rename_i g; have g:= eq_nil_of_length_eq_zero g; rw[g]; exact split_inclusive_substring_EQ_ss_nil
  have gss: ss.length > 0 := by omega
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs];
  unfold split_inclusive_substring split_inclusive_substring_def list_substring_charIndex
  unfold list_substring_charIndex_aux split_at_charIndex_list split_at_charIndex_list_aux
  have : substring_charIndex [] ss = none := substring_charIndex_of_nil gss; rw[this]
  simp only [gt_iff_lt, gss, ↓reduceDIte, map_nil]
  unfold split_inclusive_substring; simp only [gt_iff_lt, gss, ↓reduceDIte]
  split; rename_i gf ; rw[split_inclusive_substring_def_singleton_of_substring_charIndex_none gss gf]
  rename_i i gi; unfold split_inclusive_substring_def list_substring_charIndex list_substring_charIndex_aux
  simp only [gt_iff_lt, zero_add, dite_eq_ite]; simp only [gt_iff_lt, gss, ↓reduceDIte, zero_add]
  unfold split_at_charIndex_list split_at_charIndex_list_aux;
  simp only [map_cons, tsub_zero, cons.injEq]; rw[gi]
  simp only [↓reduceIte, map_cons, split_at_charIndex_EQ, split_at_charIndex_def, cons.injEq, true_and]
  rw[← split_inclusive_substring_def_aux_para1_elim gss]
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by
    rw[← gm, ← gl] ; simp only [length_drop]; omega
  exact ind m id1 gm


lemma split_inclusive_substring_merge: flatten (split_inclusive_substring s ss) = s :=by
  by_cases (ss.length > 0) ;
  rw[split_inclusive_substring_EQ, split_inclusive_substring_def, split_at_charIndex_list_merge]
  have: ss.length = 0 := by omega
  unfold split_inclusive_substring;
  simp only [this, gt_iff_lt, lt_self_iff_false, ↓reduceDIte, singleton_append, cons_append]
  unfold flatten; simp only [List.nil_append, foldl_cons, append_eq, List.append_nil, foldl_append, foldl_nil]
  induction s; simp only [map_nil, foldl_nil]
  rename_i h t ind
  simp only [map_cons, foldl_cons, append_eq, List.nil_append]
  rw[fold_append_para1_elim, ind]; simp only [singleton_append]



/-
Function: split
From: str::core::split
Description: https://doc.rust-lang.org/std/primitive.str.html#method.split
-/

def split_char_filter_aux (s: Str) (f: Char → Bool) (w: Str) := match s with
  | [] => [w]
  | h::t => if f h then w::split_char_filter_aux t f []
            else split_char_filter_aux t f (w++[h])

def split_char_filter (s: Str) (f: Char → Bool) := split_char_filter_aux s f []

def split_char_filter_def (s: Str) (f: Char → Bool) := let si := (split_inclusive_char_filter s f)
                  (List.map (fun x : Str => x.dropLast) si.dropLast) ++ si.drop (si.length - 1)

lemma flatten_split_char_filter_aux_para1_append:
      List.foldl List.append [] (split_char_filter_aux s f (v::u) ) = v::(List.foldl List.append [] (split_char_filter_aux s f u)) :=by
  induction s generalizing v u;
  simp only [split_char_filter_aux, List.nil_append, foldl_cons, append_eq, foldl_nil, List.append_nil]
  rename_i h t ind
  simp only [split_char_filter_aux, List.nil_append, singleton_append]
  split;
  simp only [singleton_append, foldl_cons, append_eq, List.nil_append, List.append_nil]; rw[fold_append_cons]
  have: v :: u ++ [h] = v :: (u ++ [h]) :=by simp only [cons_append]
  rw[this, ind]

lemma split_char_filter_aux_para1_append:
      split_char_filter_aux s f v = hl::tl → split_char_filter_aux s f (w++v) = (w ++ hl)::tl := by
  induction s generalizing w v
  simp only [split_char_filter_aux, cons.injEq, and_imp]
  intro g1 g2 ; rw[← g1, g2]; simp only [List.append_nil, and_self]
  rename_i h t ind
  simp only [split_char_filter_aux, List.nil_append]
  split; simp only [cons.injEq, append_cancel_left_eq, imp_self];
  have : w ++ v ++ [h] = w ++ (v ++ [h]) := by simp only [List.append_assoc]
  rw[this]; exact ind

lemma split_char_filter_to_aux:
      split_char_filter s f = hl::tl → split_char_filter_aux s f w = (w ++ hl)::tl := by
  unfold split_char_filter
  have : w = w ++ [] := by simp only [List.append_nil]
  rw(config:={occs:=.pos [1]})[this]; exact split_char_filter_aux_para1_append

lemma split_char_filter_aux_para1_eq_length:  (split_char_filter_aux s f w).length =  (split_char_filter_aux s f u).length :=by
  induction s generalizing w u
  simp only [split_char_filter_aux, length_append, List.length_singleton]
  rename_i h t ind
  unfold split_char_filter_aux; split;
  simp only [List.append_assoc, singleton_append, length_append, length_cons]
  exact ind

lemma split_char_filter_aux_ne_nil : split_char_filter_aux s f w ≠ [] :=by
  induction s generalizing w
  simp only [split_char_filter_aux, ne_eq, not_false_eq_true, not_sym]
  rename_i h t ind
  unfold  split_char_filter_aux
  split; simp only [ne_eq, not_false_eq_true, not_sym]; exact ind

lemma split_char_filter_ne_nil : split_char_filter s f ≠ [] :=by
  unfold split_char_filter; exact split_char_filter_aux_ne_nil


def split_char_filter_aux_def (s: Str) (f: Char → Bool) (w: Str) := let si := (split_inclusive_char_filter_aux s f w)
                  (List.map (fun x : Str => x.dropLast) si.dropLast) ++ si.drop (si.length - 1)

lemma split_char_filter_aux_EQ : split_char_filter_aux s f w = split_char_filter_aux_def s f w :=by
  induction s generalizing w
  unfold  split_char_filter_aux  split_char_filter_aux_def  split_inclusive_char_filter_aux
  simp only [dropLast_single, map_nil, List.length_singleton, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, drop_zero, List.nil_append]
  rename_i h t ind
  unfold  split_char_filter_aux  split_char_filter_aux_def  split_inclusive_char_filter_aux
  have g1: split_inclusive_char_filter_aux t f [] ≠ []:= split_inclusive_char_filter_aux_ne_nil
  split; simp only [length_cons, succ_sub_succ_eq_sub, tsub_zero]
  rw[dropLast_cons_of_ne_nil g1];
  have: (split_inclusive_char_filter_aux t f []).length = succ ((split_inclusive_char_filter_aux t f []).length -1) :=by
    have: (split_inclusive_char_filter_aux t f []).length ≠ 0 := by
      by_contra; rename_i gc; have gc:= eq_nil_of_length_eq_zero gc
      simp only [gc, ne_eq, not_true_eq_false] at g1
    omega
  rw[this]; simp only [map_cons, dropLast_concat, drop_succ_cons, cons_append, cons.injEq, true_and]
  rw[← split_char_filter_aux_def, ind]
  simp only; rw[← split_char_filter_aux_def, ind]

theorem split_char_filter_EQ : split_char_filter s f = split_char_filter_def s f :=by
  unfold split_char_filter split_char_filter_def split_inclusive_char_filter
  rw[← split_char_filter_aux_def]; apply split_char_filter_aux_EQ

-- Concatting all strings in "split_char_filter s f" is equal to remove all c not satisfying the filter f in s
-- The second condition ensures that if there are 2 consecutive chars in s that satisfying f, an empty string is put into the return list
theorem split_char_filter_append_length: (flatten (split_char_filter s f) = List.filter (fun a => ! f a) s)
      ∧ ((split_char_filter s f).length = (List.filter f s).length + 1) :=by
  unfold flatten
  induction s
  simp only [split_char_filter, split_char_filter_aux, List.nil_append, foldl_cons, append_eq,
    List.append_nil, foldl_nil, filter_nil, List.length_singleton, length_nil, zero_add, and_self]
  rename_i h t ind
  constructor
  simp only [split_char_filter, split_char_filter_aux, List.nil_append]
  split; unfold List.filter; rename_i gk; simp only [gk, Bool.not_true]
  rw[ ← split_char_filter];
  simp only [singleton_append, foldl_cons, append_eq, List.append_nil, ind]
  unfold filter; rename_i g; simp only [g, Bool.not_false]
  rw[flatten_split_char_filter_aux_para1_append]; rw[← split_char_filter, ind.left]
  --length
  simp only [split_char_filter, split_char_filter_aux, filter];
  split; rename_i gf; simp only [List.nil_append, gf, length_cons]
  rw[ ← split_char_filter]
  simp only [singleton_append, length_cons, ind.right]
  rename_i gf; simp only [List.nil_append, gf, length_cons]
  have : (split_char_filter_aux t f [h]).length  = (split_char_filter_aux t f []).length:= by
    apply split_char_filter_aux_para1_eq_length
  rw[this, ← split_char_filter, ind.right]


lemma split_char_filter_aux_singleton_of_length:
      (split_char_filter_aux s f w).length = 1 → split_char_filter_aux s f w = [w++s]:=by
  induction s generalizing w
  unfold split_char_filter_aux; simp only [List.length_singleton, List.append_nil, forall_true_left]
  rename_i h t ind
  unfold split_char_filter_aux; split
  simp only [length_cons, succ.injEq, cons.injEq]
  intro g; have g:= List.eq_nil_of_length_eq_zero g
  simp only [split_char_filter_aux_ne_nil, not_false_eq_true, not_sym] at g
  intro g; rw[ind g]; simp only [List.append_assoc, singleton_append]

lemma split_char_filter_singleton_of_length:
      (split_char_filter s f).length = 1 → split_char_filter s f = [s]:=by
  unfold split_char_filter; apply split_char_filter_aux_singleton_of_length

lemma split_char_filter_aux_flatten:
      flatten (split_char_filter_aux s f w) = w ++ flatten (split_char_filter s f) :=by
  induction s generalizing w
  unfold split_char_filter_aux flatten split_char_filter split_char_filter_aux;
  simp only [foldl_cons, append_eq, List.nil_append, foldl_nil, List.append_nil]
  rename_i h t ind
  unfold split_char_filter split_char_filter_aux
  split; unfold flatten; simp only [foldl_cons, append_eq, List.nil_append, List.append_nil]
  rw[fold_append_para1_elim]
  simp only [List.nil_append]; rw[@ind [h], ind];
  simp only [List.append_assoc, singleton_append]

lemma split_inclusive_char_filter_aux_split_char_filter_aux_eq_length:
    (split_char_filter_aux s f w).length = (split_inclusive_char_filter_aux s f w).length:= by
  induction s generalizing w
  unfold split_char_filter_aux split_inclusive_char_filter_aux
  simp only [List.length_singleton]
  rename_i h t ind
  unfold split_char_filter_aux split_inclusive_char_filter_aux
  split; simp only [length_cons, ind]
  exact ind

lemma split_inclusive_char_filter_split_char_filter_eq_length:
    (split_char_filter s f).length = (split_inclusive_char_filter s f).length:= by
  unfold split_char_filter split_inclusive_char_filter
  exact split_inclusive_char_filter_aux_split_char_filter_aux_eq_length


def split_substring (s: Str) (ss: Str)   : List Str:=
  if h: ss.length > 0 then
    match _t: substring_charIndex s ss with
      | none => [s]
      | some i => (s.take i)::split_substring (s.drop (i + ss.length)) ss
  else [[]] ++ List.map (fun c => [c]) s ++ [[]]
termination_by length s
decreasing_by simp_wf; have:= substring_charIndex_terminate _t h; simp only [h, or_true, and_true, gt_iff_lt]; omega

def drop_tail (s: Str) (n: Nat) := s.take (s.length - n)

def split_substring_def (s: Str) (ss: Str) :=
  if ss.length > 0 then
    let si := (split_inclusive_substring s ss)
    (List.map (fun x : Str => drop_tail x ss.length) si.dropLast) ++ si.drop (si.length - 1)
  else [[]] ++ List.map (fun c => [c]) s ++ [[]]

lemma split_substring_last : ∃ l, (split_inclusive_substring s ss).drop ((split_inclusive_substring s ss).length - 1) = [l] :=by
  generalize gu: (split_inclusive_substring s ss).drop ((split_inclusive_substring s ss).length - 1) = u
  have lu: u.length = 1 :=by
    rw[← gu]; simp only [length_drop]
    have : ¬ (split_inclusive_substring s ss).length = 0 :=by
      by_contra ; rename_i gc; have gc:= eq_nil_of_length_eq_zero gc
      simp only [split_inclusive_substring_ne_nil, not_false_eq_true, not_sym] at gc
    omega
  cases u; simp only [length_nil, zero_ne_one, not_false_eq_true, not_sym] at lu
  rename_i hu tu; simp only [length_cons, succ.injEq] at lu; have lu:= eq_nil_of_length_eq_zero lu
  simp only [lu] at gu; simp only [lu, cons.injEq, and_true, exists_eq']

--This function return the concatenation of strings in the list of string l, but pad a string s between them
def str_concat_pad (l: List Str) (s: Str) := match l with
  | [] => []
  | h::t => match t with | [] => h | _ => h ++ s ++ (str_concat_pad t s)

lemma sub_split_substring_sound1 : s = str_concat_pad (List.map (fun c => [c]) s) [] :=by
  induction s; simp only [str_concat_pad]
  rename_i h t ind; simp only [str_concat_pad]
  split; rename_i gt; simp only [map_eq_nil] at gt
  simp only [gt]; simp only [singleton_append, cons.injEq, true_and]
  exact ind

lemma split_substring_ne_nil : split_substring s ss ≠ [] :=by
  by_cases (ss.length > 0); rename_i gss
  unfold split_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte, List.nil_append, ne_eq]
  split; simp only [not_false_eq_true, not_sym]
  simp only [singleton_append, not_false_eq_true, not_sym]
  have g: ss.length = 0 :=by omega
  have g:= eq_nil_of_length_eq_zero g; rw[g]
  simp only [split_substring, length_nil, gt_iff_lt, lt_self_iff_false, ↓reduceDIte,
    singleton_append, cons_append, ne_eq, not_false_eq_true, not_sym]


theorem split_substring_EQ: split_substring s ss = split_substring_def s ss := by
  by_cases (ss.length > 0); rename_i gss
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw[gs]
  unfold split_substring split_substring_def split_inclusive_substring
  have : substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[this]; simp only [gt_iff_lt, gss, ↓reduceDIte, ↓reduceIte, dropLast_single, map_nil,
    length_cons, length_nil, zero_add, le_refl, tsub_eq_zero_of_le, drop_zero, nil_append]
  unfold split_substring split_substring_def split_inclusive_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte]
  split;
  simp only [↓reduceIte, dropLast_single, map_nil, length_cons, length_nil, zero_add, le_refl,
    tsub_eq_zero_of_le, drop_zero, nil_append]
  rename_i i gi;
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by
    rw[← gm, ← gl]; simp only [length_drop]; omega
  have ind:=ind m id1 gm ;
  have g1: split_inclusive_substring (List.drop (i + ss.length) s) ss ≠ []:= split_inclusive_substring_ne_nil
  rw[ dropLast_cons_of_ne_nil g1]
  simp only [ind, map_cons, length_cons, succ_sub_succ_eq_sub, tsub_zero, cons_append, cons.injEq]
  have gi:= substring_charIndex_some_sound.mp gi; unfold is_first_substringcharIndex at gi
  have gi:= gi.left; unfold is_substringcharIndex at gi; obtain⟨u1, u2, gi⟩ := gi
  rw[gi.left, ← gi.right, drop_tail];
  simp only [List.append_assoc, take_left, length_take, length_append, ge_iff_le,
    add_le_add_iff_left, le_add_iff_nonneg_right, _root_.zero_le, min_eq_left,
    add_tsub_cancel_right]
  have : List.take (u1.length + ss.length) (u1 ++ (ss ++ u2)) = u1 ++ ss := by
    have i1: u1 ++ (ss ++ u2) = u1 ++ ss ++ u2:= by simp only [List.append_assoc]
    have i2: (u1.length + ss.length) = (u1 ++ ss).length + 0 := by simp only [length_append, add_zero]
    rw[i1, i2, List.take_append]; simp only [take_zero, List.append_nil]
  rw[this]; simp only [take_left, length_cons, succ_sub_succ_eq_sub, tsub_zero, true_and]
  unfold split_substring_def;
  have: (split_inclusive_substring (List.drop (u1.length + ss.length) (u1 ++ (ss ++ u2))) ss).length
    = succ ((split_inclusive_substring (List.drop (u1.length + ss.length) (u1 ++ (ss ++ u2))) ss).length -1) :=by
    have : (split_inclusive_substring (List.drop (u1.length + ss.length) (u1 ++ (ss ++ u2))) ss).length ≠ 0 :=by
      by_contra; rename_i gc; have gc:= eq_nil_of_length_eq_zero gc
      have: ¬  split_inclusive_substring (List.drop (u1.length + ss.length) (u1 ++ (ss ++ u2))) ss = [] := by
        apply split_inclusive_substring_ne_nil
      contradiction
    omega
  rw[this]
  simp only [gt_iff_lt, gss, ↓reduceIte, drop_append, drop_left, map_dropLast,succ_eq_add_one, drop_succ_cons]
  rename_i g; unfold split_substring split_substring_def;
  simp only [gt_iff_lt, g, ↓reduceDIte, singleton_append, cons_append, ↓reduceIte]


theorem split_substring_reconstruct (g: sl = split_substring s ss) (gss: ss.length > 0):
    (s = str_concat_pad sl ss) ∧ (∀ sm ∈ sl, ¬ contains_substring sm ss) := by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s sl
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs
  rw [gs] at g;
  unfold split_substring at g
  simp only [length_cons, gt_iff_lt, zero_lt_succ, ↓reduceDIte,  List.nil_append,
    drop_nil,  take_nil, gss] at g
  split at g; rw[g]; simp only [gs, str_concat_pad]
  rename_i gsk; have i1: substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  simp only [gsk, not_false_eq_true, not_sym] at i1
  simp only [mem_singleton, Bool.not_eq_true, forall_eq, true_and]
  have gsk:= substring_charIndex_none_sound gsk; simp only [gsk]
  rename_i g0; unfold substring_charIndex substring_charIndex_aux at g0
  cases ss; simp only [length_nil, gt_iff_lt, lt_self_iff_false] at gss
  simp only [not_false_eq_true, not_sym] at g0
  unfold split_substring at g
  split at g; split at g ; rw[g];
  simp only [str_concat_pad, mem_singleton, Bool.not_eq_true, forall_eq, true_and]
  rename_i g0; have g0:= substring_charIndex_none_sound g0; simp only [g0]
  rename_i gs gss _ _;  rename_i i gi
  generalize gu: (List.drop (i + ss.length) s) = u
  generalize gsu: split_substring u ss = su
  generalize gm: u.length = m
  rw[gu, gsu] at g
  symm at gl gu gsu
  have i1: m < n:= by
    rw[gl, ← gm,  gu]; simp only [length_drop]; omega
  have ind:= ind m i1 gsu gm
  rw[g]; simp only [str_concat_pad, append_eq, List.nil_append, List.append_assoc]
  split; have : split_substring u ss ≠ [] := split_substring_ne_nil
  rw[← gsu] at this ; contradiction;
  constructor; rw[← ind.left]
  have e1: List.take i s ++ ss = List.take (i + ss.length) s:= by
    have e11:= substring_charIndex_some_sound.mp gi
    unfold is_first_substringcharIndex at e11
    have e11:= e11.left
    unfold is_substringcharIndex at e11
    obtain ⟨s0,s2, g02⟩ := e11
    have e12: List.IsPrefix s0 s :=by rw[g02.left]; simp only [List.append_assoc, prefix_append]
    have e12: s.take i = s0 := by rw[← g02.right]; apply prefix_eq_take e12
    rw[e12]
    have e14: (i + ss.length) = (s0 ++ ss).length :=by simp only [length_append, g02]
    symm; rw[e14]; apply prefix_eq_take; rw[g02.left]; apply prefix_append
  rw[← List.append_assoc, e1, gu]; simp only [take_append_drop]
  simp only [singleton_append, mem_cons, forall_eq_or_imp]
  constructor
  exact not_contain_substring_until_substring_charIndex gss gi
  exact ind.right
  contradiction

lemma split_substring_singleton_of_length (gss: ss.length>0):
      (split_substring s ss).length = 1 → split_substring s ss = [s]:=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i n _
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs
  rw [gs]; unfold split_substring
  have gk:= @substring_charIndex_of_nil ss gss; rw[gk]
  simp only [gt_iff_lt, gss, ↓reduceDIte, List.length_singleton, forall_true_left]
  unfold split_substring; simp only [gt_iff_lt, gss, ↓reduceDIte]
  split; simp only [List.length_singleton, forall_true_left]
  simp only [length_cons, succ.injEq, cons.injEq]
  intro gc; have gc:= List.eq_nil_of_length_eq_zero gc
  simp only [split_substring_ne_nil, not_false_eq_true, not_sym] at gc


lemma split_substring_singleton_of_substring_charIndex :
      substring_charIndex s ss = none → split_substring s ss = [s]:=by
  by_cases (ss.length=0); rename_i gc; have gc:= eq_nil_of_length_eq_zero gc
  rw[gc] ; unfold substring_charIndex substring_charIndex_aux;
  simp only [contains_substring.match_1.eq_1, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  have gss: ss.length>0 :=by omega
  intro g
  unfold split_substring; rw[g]; simp only [gt_iff_lt, gss, ↓reduceDIte]

lemma split_inclusive_substring_split_substring_eq_length (gss: ss.length>0):
    (split_substring s ss).length = (split_inclusive_substring s ss).length:= by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs; rw [gs];
  unfold split_substring split_inclusive_substring
  have gc:= @substring_charIndex_of_nil ss gss; rw[gc]
  simp only [gt_iff_lt, gss, ↓reduceDIte, length_singleton]
  unfold split_substring split_inclusive_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte]
  split; simp only [List.length_singleton]
  simp only [length_cons, succ.injEq]; rename_i i _
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n := by rw[← gm, ← gl]; simp only [length_drop]; omega
  exact ind m id1 gm



--#eval split_substring "lion::tiger::leopard".data "::".data
--#eval split_char_filter "lionXXtigerXleopardXX".data Char.isUpper

def split (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => split_char_filter s (fun x => x = c)
  | Pattern.ListChar l => split_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => split_char_filter s f
  | Pattern.WholeString ss => split_substring s ss


/-
Function: rsplit
From: str::core::rsplit
Description: https://doc.rust-lang.org/std/primitive.str.html#method.rsplit
-/

def rsplit (s: Str) (P: Pattern) := List.reverse (split s P)


/-
Function: splitn
From: str::core::splitn
Description: https://doc.rust-lang.org/std/primitive.str.html#method.splitn
-/


def splitn_char_filter_aux (s: Str) (n: Nat) (f: Char → Bool)  (w: Str)  :=
  if n = 0 then [] else if n = 1 then [w++s] else
    match s with
      | [] => [w]
      | h::t => if f h then w::splitn_char_filter_aux t (n-1) f []
                else splitn_char_filter_aux t n f (w++[h])

def splitn_char_filter (s: Str) (n: Nat) (f: Char → Bool)  := splitn_char_filter_aux s n f []

def splitn_char_filter_def (s: Str) (n: Nat) (f: Char → Bool)  :=
    if n = 0 then [] else
      if (split_char_filter s f).length ≤ n then split_char_filter s f else
      (split_char_filter s f).take (n-1) ++ [flatten ((split_inclusive_char_filter s f).drop (n-1))]

--#eval splitn_char_filter_def "baafgamgwadd".data (fun x => x = 'a' ) 4
--#eval splitn_char_filter "baafgamgwadd".data (fun x => x = 'a' ) 4


def splitn_char_filter_aux_def (s: Str) (n: Nat) (f: Char → Bool)  (w: Str) :=
      if (split_char_filter_aux s f w).length ≤ n then split_char_filter_aux s f w else
      (split_char_filter_aux s f w).take (n-1) ++ [flatten ((split_inclusive_char_filter_aux s f w).drop (n-1))]

--#eval splitn_char_filter_aux "abddfaa".data (fun x => x = 'a') 1 "bcd".data
--#eval splitn_char_filter_aux_def "abddfaa".data (fun x => x = 'a') 1 "bcd".data

theorem splitn_char_filter_aux_EQ (gn: n>0): splitn_char_filter_aux s n f w = splitn_char_filter_aux_def s n f w:=by
  induction s generalizing n w
  unfold splitn_char_filter_aux_def splitn_char_filter_aux
  have : ¬ n = 0 :=by omega
  simp only [this, not_false_eq_true, not_sym, ↓reduceIte, ite_self]
  unfold split_char_filter_aux
  have : n ≥ 1 :=by omega
  simp only [List.append_nil, ite_self, length_cons, length_nil, reduceSucc, this, ↓reduceIte]
  rename_i h t ind
  unfold splitn_char_filter_aux
  have : ¬ n = 0 :=by omega
  simp only [this, not_false_eq_true, not_sym, ↓reduceIte, List.nil_append]
  by_cases (n=1); rename_i gn; simp only [gn, ↓reduceIte]
  unfold splitn_char_filter_aux_def; split
  have gsl: (split_char_filter_aux (h :: t) f w).length = 1 := by
    by_cases ((split_char_filter_aux (h :: t) f w).length =0)
    rename_i gc; have gc:=List.eq_nil_of_length_eq_zero gc
    simp only [split_char_filter_aux_ne_nil, not_false_eq_true, not_sym] at gc
    omega
  rw[split_char_filter_aux_singleton_of_length gsl]
  simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, take_zero, drop_zero, List.nil_append,
    cons.injEq, and_true]
  rw[split_inclusive_char_filter_aux_flatten, split_inclusive_char_filter_merge]
  rename_i gn ; simp only [gn, not_false_eq_true, not_sym, ↓reduceIte]
  split; unfold splitn_char_filter_aux_def; split; unfold split_char_filter_aux
  rename_i gf _; simp only [gf, ↓reduceIte, cons.injEq, true_and]
  have : n-1>0 := by omega;
  have ind:= @ind (n-1) [] this; rw[ind]
  rename_i gsl
  have : (split_char_filter_aux t f []).length ≤ n - 1 := by
    rw[@split_char_filter_aux_para1_eq_length (h::t) f w []] at gsl
    rw[split_char_filter_aux] at gsl
    simp only [gf, ↓reduceIte, length_cons] at gsl; omega
  unfold splitn_char_filter_aux_def
  simp only [this, ↓reduceIte];
  unfold  split_char_filter_aux split_inclusive_char_filter_aux
  rename_i gf gsl; simp only [gf, ↓reduceIte, List.nil_append]
  have : n - 1 = succ (n-2):= by omega
  rw[this]; simp only [take_cons_succ, drop_succ_cons, cons_append, cons.injEq, true_and]
  rw[← this]; have : n-1>0 := by omega;
  have ind:= @ind (n-1) [] this
  rw[ind, splitn_char_filter_aux_def]
  have :¬ (split_char_filter_aux t f []).length ≤ n - 1 := by
    rw[@split_char_filter_aux_para1_eq_length (h::t) f w []] at gsl
    rw[split_char_filter_aux] at gsl
    simp only [gf, ↓reduceIte, length_cons, not_le] at gsl; omega
  simp only [this, ↓reduceIte]
  have : n - 1 - 1 = n - 2 := by omega
  rw[this]
  unfold splitn_char_filter_aux_def; split; rename_i gf gsl
  unfold split_char_filter_aux;
  simp only [gf, not_false_eq_true, not_sym, ↓reduceIte, List.nil_append]
  rw[ind, splitn_char_filter_aux_def]
  have : (split_char_filter_aux t f (w ++ [h])).length ≤ n:=by
    rw[@split_char_filter_aux_para1_eq_length (h::t) f w (w ++ [h])] at gsl
    rw[split_char_filter_aux] at gsl
    simp only [gf, not_false_eq_true, not_sym, ↓reduceIte, List.append_assoc, singleton_append] at gsl;
    rw[@split_char_filter_aux_para1_eq_length t f (w ++ [h, h]) (w ++ [h])] at gsl
    omega
  simp only [this, ↓reduceIte]; assumption
  rename_i gf gsl;
  unfold  split_char_filter_aux split_inclusive_char_filter_aux
  simp only [gf, not_false_eq_true, not_sym, ↓reduceIte]
  have : ¬ (split_char_filter_aux t f (w ++ [h])).length ≤ n:=by
    rw[@split_char_filter_aux_para1_eq_length (h::t) f w (w ++ [h])] at gsl
    rw[split_char_filter_aux] at gsl
    simp only [gf, not_false_eq_true, not_sym, ↓reduceIte, List.append_assoc, singleton_append, not_le] at gsl;
    rw[@split_char_filter_aux_para1_eq_length t f (w ++ [h, h]) (w ++ [h])] at gsl;  omega
  rw[ind, splitn_char_filter_aux_def];
  simp only [this, ↓reduceIte]; assumption


theorem splitn_char_filter_EQ : splitn_char_filter s n f = splitn_char_filter_def s n f :=by
  unfold splitn_char_filter  splitn_char_filter_def split_char_filter split_inclusive_char_filter
  rw[← splitn_char_filter_aux_def];
  split; rename_i gn; unfold splitn_char_filter_aux; simp only [gn, ↓reduceIte]
  have gn: n > 0 := by omega
  apply splitn_char_filter_aux_EQ gn

lemma splitn_char_filter_ne_nil (gn: n>0): splitn_char_filter s n f ≠ [] := by
  rw[splitn_char_filter_EQ, splitn_char_filter_def]
  have: ¬ n = 0 := by omega
  simp only [this, not_false_eq_true, not_sym, ↓reduceIte, ne_eq]
  split; exact split_char_filter_ne_nil;
  simp only [ne_eq, append_eq_nil, take_eq_nil_iff, cons_ne_self, and_false, not_false_eq_true, not_sym]

def splitn_substring(s: Str) (n: Nat) (ss: Str)   : List Str:=
  if n = 0 then [] else if n=1 then [s] else
        if _h1: ss.length > 0 then
          match _t: substring_charIndex s ss with
            | none => [s]
            | some i => (s.take i)::splitn_substring (s.drop (i + ss.length)) (n-1) ss
        else [[]] ++ List.map (fun c => [c]) (s.take (n-2)) ++ [(s.drop (n-2))]
termination_by length s
decreasing_by simp_wf; have:= substring_charIndex_terminate _t _h1; simp only [_h1, or_true, and_true, gt_iff_lt]; omega

def splitn_substring_def (s: Str) (n: Nat) (ss: Str)  :=
  if n > 0 then
      if (split_substring s ss).length ≤ n then split_substring s ss else
      (split_substring s ss).take (n-1) ++ [flatten ((split_inclusive_substring s ss).drop (n-1))]
  else []

--#eval splitn_substring_def "abcd".data 9 []
--#eval splitn_substring "abcd".data 9 []

lemma sub_splitn_substring_EQ_ss_nil1 : s = foldl List.append [] (map (fun c ↦ [c]) s) :=by
  induction s
  simp only [map_nil, foldl_nil]
  rename_i h t ind
  simp only [map_cons, foldl_cons, append_eq, nil_append]
  rw[fold_append_para1_elim]
  simp only [singleton_append, cons.injEq, true_and]
  exact ind

lemma sub_splitn_substring_EQ_ss_nil2 (g: n ≤  s.length): drop n s = flatten (drop n (map (fun c ↦ [c]) s)):=by
  induction s generalizing n
  simp only [drop_nil, flatten, map_nil, foldl_nil]
  rename_i h t ind
  cases n; simp only [drop_zero, flatten, map_cons, foldl_cons, append_eq, nil_append]
  rw[fold_append_para1_elim]; simp only [singleton_append, cons.injEq, true_and]
  exact sub_splitn_substring_EQ_ss_nil1
  rename_i n; simp only [drop_succ_cons, map_cons]
  simp only [length_cons, add_le_add_iff_right] at g
  exact ind g

lemma splitn_substring_EQ_ss_nil (gn: n > 0) : splitn_substring s n [] =  splitn_substring_def s n [] :=by
  unfold splitn_substring splitn_substring_def
  simp only [length_nil, gt_iff_lt, lt_self_iff_false, ↓reduceDIte, map_take, singleton_append,
    cons_append, gn, ↓reduceIte, split_substring, length_cons, length_append, length_map,
    length_singleton, split_inclusive_substring]
  have :¬ n= 0 := by omega
  simp only [this, not_false_eq_true, not_sym, ↓reduceIte, nil_append, zero_add]
  split; split; omega; rename_i gn _;
  simp only [gn, le_refl, tsub_eq_zero_of_le, take_zero,
    flatten, drop_zero, foldl_cons, append_eq, append_nil, nil_append, cons.injEq, and_true]
  exact sub_splitn_substring_EQ_ss_nil1
  split; simp only [cons.injEq, true_and];
  rw[take_all_of_le, drop_eq_nil_iff_le.mpr]; omega; simp only [length_map]; omega
  have: n - 1 = succ (n-2) :=by omega
  rw[this]; simp only [succ_eq_add_one, take_cons_succ, drop_succ_cons, cons_append, cons.injEq, true_and]
  rw[take_append_eq_append_take]; simp only [length_map, append_assoc, append_cancel_left_eq]
  have: n - 2 - length s = 0:=by omega
  simp only [this, take_zero, nil_append, cons.injEq, and_true]
  apply sub_splitn_substring_EQ_ss_nil2; omega

theorem splitn_substring_EQ  : splitn_substring s n ss =  splitn_substring_def s n ss  :=by
  by_cases (n>0); rename_i gn
  by_cases (ss.length > 0); rename_i gss
  generalize gls: s.length = ls
  induction ls using Nat.strong_induction_on generalizing s n
  rename_i ls ind
  have gn:¬ n = 0 :=by omega
  rename_i gn0
  by_cases (ls = 0); rename_i g1; rw[g1] at gls
  have gls:= List.eq_nil_of_length_eq_zero gls; rw[gls];
  unfold splitn_substring splitn_substring_def  split_substring split_inclusive_substring
  have gk:= @substring_charIndex_of_nil ss gss
  have gn1: n ≥ 1 := by omega
  rw[gk]; simp only [gn, not_false_eq_true, not_sym, ↓reduceIte, gt_iff_lt, gss, ↓reduceDIte,
    ite_self, gn0, length_singleton, gn1]
  unfold splitn_substring; simp only [gn, not_false_eq_true, not_sym, ↓reduceIte, gt_iff_lt, gss,↓reduceDIte]
  split; unfold splitn_substring_def; simp only [gt_iff_lt, gn0, ↓reduceIte]; rename_i gn; rw[gn]; split
  have: (split_substring s ss).length = 1 := by
    by_cases (split_substring s ss).length = 0; rename_i gc
    have gc:= List.eq_nil_of_length_eq_zero gc
    simp only [split_substring_ne_nil, not_false_eq_true, not_sym] at gc
    omega
  simp only [split_substring_singleton_of_length gss this, List.length_singleton, le_refl, ↓reduceIte];
  simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, take_zero, drop_zero,
    split_inclusive_substring_merge, List.nil_append]
  split; rename_i gc; unfold splitn_substring_def
  simp only [split_substring_singleton_of_substring_charIndex gc, List.length_singleton]
  have : n ≥ 1 := by omega
  simp only [gt_iff_lt, gn0, ↓reduceIte, this]; rename_i i gi
  unfold splitn_substring_def  split_inclusive_substring;
  simp only [gt_iff_lt, gn0, ↓reduceIte,singleton_append, dite_eq_ite]
  split; unfold split_substring; rw[gi]; simp only [gt_iff_lt, gss, ↓reduceDIte, cons.injEq, true_and]
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < ls:= by rw[← gm, ← gls]; simp only [length_drop]; omega
  have id0: n - 1 > 0 := by omega
  have ind:= ind m id1 id0 gm; rw[ind]; unfold splitn_substring_def; simp only [id0, ↓reduceIte]
  have : (split_substring (List.drop (i + ss.length) s) ss).length ≤ n - 1 :=by
    rename_i gc ; unfold split_substring at gc; rw[gi] at gc
    simp only [gt_iff_lt, gss, ↓reduceDIte, length_cons] at gc; omega
  simp only [this, ↓reduceIte]
  have : n - 1 = succ (n-2) :=by omega
  rw[split_substring, gi, this];
  simp only [gt_iff_lt, gss, ↓reduceDIte, take_cons_succ, drop_succ_cons, cons_append, cons.injEq,true_and]
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < ls:= by rw[← gm, ← gls]; simp only [length_drop]; omega
  have id0: n - 1 > 0 := by omega
  have ind:= ind m id1 id0 gm; rw[← this,ind]; unfold splitn_substring_def
  have: ¬ (split_substring (List.drop (i + ss.length) s) ss).length ≤ n - 1 := by
    rename_i gc ; unfold split_substring at gc; rw[gi] at gc
    simp only [gt_iff_lt, gss, ↓reduceDIte, length_cons] at gc; omega
  simp only [gt_iff_lt, id0, ↓reduceIte, this]
  have : n - 1 -1 = n - 2 :=by omega
  rw[this]
  have g: length ss = 0:= by omega
  have g:= eq_nil_of_length_eq_zero g; rw[g]
  exact splitn_substring_EQ_ss_nil (by omega)
  have gn: n = 0:=by omega
  simp only [gn, splitn_substring, ↓reduceIte, splitn_substring_def, gt_iff_lt, lt_self_iff_false]

lemma splitn_substring_ne_nil (gn: n > 0):  splitn_substring s n ss ≠ [] := by
  rw[splitn_substring_EQ, splitn_substring_def]; simp only [gt_iff_lt, gn, ↓reduceIte, ne_eq]
  split; exact split_substring_ne_nil;
  simp only [ne_eq, append_eq_nil, take_eq_nil_iff, cons_ne_self, and_false, not_false_eq_true, not_sym]


--#eval splitn_by_substring "lionXXtigerXXleopardXXcatXXdog".data "XX".data 3

def splitn (s: Str) (n: Nat) (P: Pattern) := match P with
  | Pattern.SingleChar c => splitn_char_filter s n (fun x => x = c)
  | Pattern.ListChar l => splitn_char_filter s n (fun x => x ∈ l)
  | Pattern.FilterFunction f => splitn_char_filter s n f
  | Pattern.WholeString ss => splitn_substring s n ss

/-
Function: rsplitn
From: str::core::rsplitn
Description: https://doc.rust-lang.org/std/primitive.str.html#method.rsplitn
-/


def rsplitn_char_filter (s: Str) (f: Char → Bool) (n: Nat) := List.map (fun x: Str => x.reverse) (splitn_char_filter (s.reverse) n f)

def rsplitn_substring (s: Str) (ss: Str) (n: Nat) := List.map (fun x: Str => x.reverse) (splitn_substring (s.reverse) n (ss.reverse))

def rsplitn (s: Str) (P: Pattern) (n: Nat):= match P with
  | Pattern.SingleChar c => rsplitn_char_filter s (fun x => x = c) n
  | Pattern.ListChar l => rsplitn_char_filter s (fun x => x ∈ l) n
  | Pattern.FilterFunction f => rsplitn_char_filter s f n
  | Pattern.WholeString ss => rsplitn_substring s ss n

/-
Function: split_once
From: str::core::split_once
Description: https://doc.rust-lang.org/std/primitive.str.html#method.split_once
-/


def split_once (s: Str) (P: Pattern)  := splitn s 1 P

/-
Function: rsplit_once
From: str::core::rsplit_once
Description: https://doc.rust-lang.org/std/primitive.str.html#method.rsplit_once
-/

def rsplitn_once (s: Str) (P: Pattern)  := rsplitn s P 1


/-
Function: split_ascii_whitespace
From: str::core::split_ascii_whitespace
Description: https://doc.rust-lang.org/std/primitive.str.html#method.split_ascii_whitespace
-/

def split_ascii_whitespace_aux (s: Str) (w: Str) (prespace: Bool): List Str := match s with
  | [] => if prespace = false then [w] else []
  | h::t => if is_ascii_whitespace h then
          if prespace = false then w::split_ascii_whitespace_aux t [] true else split_ascii_whitespace_aux t []  true
          else split_ascii_whitespace_aux t (w++[h]) false

def split_ascii_whitespace (s: Str) := split_ascii_whitespace_aux s [] true

def split_ascii_whitespace_def (s: Str) := filter (fun a: Str => a.length > 0) (split_char_filter s is_ascii_whitespace)

--#eval split_ascii_whitespace "   abc  fsdf  f  ".data
--#eval split_ascii_whitespace "   ".data
--#eval split_ascii_whitespace_def "   abc  fsdf  f  ".data


lemma split_ascii_whitespace_aux_false_para1_append: split_ascii_whitespace_aux s w false = hs::ts →  split_ascii_whitespace_aux s (v++w) false = (v++hs)::ts:=by
  induction s generalizing w v
  unfold split_ascii_whitespace_aux
  split; simp only [cons.injEq, append_cancel_left_eq, imp_self];
  simp only [↓reduceIte, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ind
  unfold split_ascii_whitespace_aux
  split; simp only [↓reduceIte, cons.injEq, append_cancel_left_eq, imp_self]
  have : v ++ w ++ [h] = v ++ (w ++ [h]) :=by simp only [List.append_assoc]
  rw[this]; exact ind

lemma split_ascii_whitespace_aux_false_ne_nil  : split_ascii_whitespace_aux s w false ≠ [] := by
  induction s generalizing w
  simp only [split_ascii_whitespace_aux, ↓reduceIte, ne_eq, not_false_eq_true, not_sym]
  rename_i h t ind
  simp only [split_ascii_whitespace_aux, ↓reduceIte, ne_eq]
  split; simp only [not_false_eq_true]; exact ind

lemma split_ascii_whitespace_aux_para2_elim_case1: (¬ is_ascii_whitespace a) → split_ascii_whitespace_aux (a::s) w false = split_ascii_whitespace_aux (a::s) w true := by
  intro g; unfold split_ascii_whitespace_aux
  simp only [g, not_false_eq_true, not_sym, ↓reduceIte]

lemma split_ascii_whitespace_aux_para2_elim_case2: (is_ascii_whitespace a) → split_ascii_whitespace_aux (a::s) w false = w::split_ascii_whitespace_aux (a::s) w true := by
  intro g; unfold split_ascii_whitespace_aux
  simp only [g, not_false_eq_true, not_sym, ↓reduceIte]

lemma split_char_filter_aux_head_ne_nil (ga: ¬ f a) : split_char_filter_aux  (a :: s) f w = hsp :: tsp → hsp ≠ [] :=by
  induction s generalizing a w hsp tsp
  simp only [split_char_filter_aux, ga, not_false_eq_true, not_sym, ↓reduceIte, cons.injEq, ne_eq, and_imp]
  intro g; simp only [← g, append_eq_nil, and_false, not_false_eq_true, not_sym, implies_true]
  rename_i h t ind
  unfold split_char_filter_aux; simp only [ga, not_false_eq_true, not_sym, ↓reduceIte, ne_eq]
  by_cases (f h); rename_i gc; simp only [split_char_filter_aux, gc, ↓reduceIte, cons.injEq, and_imp]
  intro g; simp only [← g, append_eq_nil, and_false, not_false_eq_true, not_sym, implies_true]
  rename_i gc; exact ind gc

theorem split_ascii_whitespace_EQ: split_ascii_whitespace s = split_ascii_whitespace_def s := by
  induction s
  unfold split_ascii_whitespace split_ascii_whitespace_aux split_ascii_whitespace_def split_char_filter split_char_filter_aux
  simp only [not_false_eq_true, not_sym, ↓reduceIte, gt_iff_lt, decide_False, filter_cons_of_neg,
    filter_nil]
  unfold filter; simp only [length_nil, lt_self_iff_false, decide_False, filter_nil]
  rename_i h t ind
  by_cases (is_ascii_whitespace h) ; rename_i gc;
  have e1: split_ascii_whitespace (h :: t) =  split_ascii_whitespace t:= by
    simp only [split_ascii_whitespace, split_ascii_whitespace_aux, gc, ↓reduceIte, not_false_eq_true, not_sym]
  unfold split_ascii_whitespace_def split_char_filter split_char_filter_aux
  simp only [gt_iff_lt, gc, ↓reduceIte, decide_False, not_false_eq_true, not_sym,
    filter_cons_of_neg]
  unfold filter; simp only [length_nil, lt_self_iff_false, decide_False]
  rw[← split_char_filter, ← split_ascii_whitespace_def, e1, ind]
  rename_i gc; unfold split_ascii_whitespace_def split_char_filter split_char_filter_aux
  simp only [gt_iff_lt, gc, not_false_eq_true, not_sym, ↓reduceIte, List.nil_append]
  generalize gsp1: split_char_filter_aux t is_ascii_whitespace [] = sp1
  cases sp1; simp only [split_char_filter_aux_ne_nil, not_false_eq_true, not_sym] at gsp1
  rename_i hsp1 tsp1; have gsp11:= @split_char_filter_aux_para1_append _ _ _ _ _ [h] gsp1
  simp only [singleton_append] at gsp11; rw[gsp11]
  simp only [length_cons, zero_lt_succ, decide_True, filter_cons_of_pos]
  unfold split_ascii_whitespace split_ascii_whitespace_aux
  simp only [gc, not_false_eq_true, not_sym, ↓reduceIte, List.nil_append]
  generalize gsp2: split_ascii_whitespace_aux t [] false = sp2
  cases sp2; simp only [split_ascii_whitespace_aux_false_ne_nil, not_false_eq_true, not_sym] at gsp2
  rename_i hsp2 tsp2; have gsp21:= @split_ascii_whitespace_aux_false_para1_append _ _ _ _  [h] gsp2
  simp only [singleton_append] at gsp21; rw[gsp21]
  unfold split_ascii_whitespace split_ascii_whitespace_def split_char_filter at ind
  rw[gsp1] at ind
  cases t; simp [split_char_filter_aux] at gsp1; simp only [split_ascii_whitespace_aux, ↓reduceIte, cons.injEq] at gsp2
  rw[← gsp1.left, ← gsp1.right, ← gsp2.right, ← gsp2.left]; simp only [filter_nil]
  rename_i ht tt
  by_cases (is_ascii_whitespace ht); rename_i gc; rw[split_ascii_whitespace_aux_para2_elim_case2 gc] at gsp2
  simp only [cons.injEq, true_and] at gsp2; rw[gsp2.right] at ind; rw[← gsp2.left, ind]
  simp only [split_char_filter_aux, gc, ↓reduceIte, cons.injEq] at gsp1; rw[← gsp1.left]
  simp only [gt_iff_lt, decide_False, not_false_eq_true, not_sym, filter_cons_of_neg]
  generalize gm: filter (fun a => decide (a.length > 0)) ([] :: tsp1) = m
  unfold filter at gm; simp only [length_nil, gt_iff_lt, lt_self_iff_false, decide_False] at gm; rw[gm]
  rename_i gc; rw[split_ascii_whitespace_aux_para2_elim_case1 gc] at gsp2; rw[gsp2] at ind
  have gc: hsp1.length > 0 := length_pos_from_not_nil.mp (split_char_filter_aux_head_ne_nil gc gsp1)
  unfold filter at ind; simp only [gt_iff_lt, gc, decide_True, cons.injEq] at ind
  simp only [ind]


lemma sub_split_ascii_whitespace_flatten1: List.foldl List.append [] (split_ascii_whitespace_aux s (v::tv) false)
        = v::List.foldl List.append [] (split_ascii_whitespace_aux s tv false) :=by
  induction s generalizing v tv
  simp only [split_ascii_whitespace_aux, ↓reduceIte, List.nil_append, foldl_cons, append_eq, foldl_nil,
    cons.injEq, true_and, split_ascii_whitespace]
  rename_i h t ind
  simp only [split_ascii_whitespace_aux, ↓reduceIte, List.nil_append, singleton_append, split_ascii_whitespace,
    not_false_eq_true, not_sym]
  split;
  simp only [singleton_append, foldl_cons, append_eq, List.nil_append]
  rw[fold_append_cons]; exact ind

lemma sub_split_ascii_whitespace_flatten2  (g: m ∈ split_ascii_whitespace_aux s w b ) (gc: b = true ∨ w ≠ [])
  :  ¬ m = [] :=by
  induction s generalizing w b
  simp only [split_ascii_whitespace_aux, List.nil_append] at g
  cases gc; rename_i gc; simp only [gc, not_false_eq_true, not_sym, ↓reduceIte, not_mem_nil] at g
  split at g; simp only [mem_singleton] at g; simp only [g]; assumption; simp only [not_mem_nil] at g
  rename_i h t ind
  simp only [split_ascii_whitespace_aux, List.nil_append] at g; split at g
  split at g;
  simp only [singleton_append, mem_cons] at g;
  rename_i gb; simp only [gb, not_false_eq_true, not_sym, ne_eq, false_or] at gc
  cases g; rename_i gw; rw[gw]; exact gc; rename_i g
  have ind:=ind g; simp only [ne_eq, not_true_eq_false, or_false, forall_true_left] at ind; exact ind
  have ind:=ind g; simp only [ne_eq, not_true_eq_false, or_false, forall_true_left] at ind; exact ind
  have ind:=ind g;simp only [not_false_eq_true, not_sym, ne_eq, append_eq_nil, and_false, or_true,
    forall_true_left] at ind; exact ind


lemma sub_split_ascii_whitespace_flatten: ((flatten (split_ascii_whitespace_aux s [] b) = List.filter (fun a => ! is_ascii_whitespace a) s))
                                  ∧ (∀ x ∈ split_ascii_whitespace s, x ≠ []):=by
  unfold flatten
  induction s generalizing b
  simp only [split_ascii_whitespace, split_ascii_whitespace_aux, not_false_eq_true, not_sym, ↓reduceIte,
    foldl_nil, filter_nil, not_mem_nil, ne_eq, IsEmpty.forall_iff, forall_const, and_self]
  split; simp only [List.nil_append, foldl_cons, append_eq, List.append_nil, foldl_nil, and_self]
  simp only [foldl_nil, and_self]
  rename_i h t ind
  simp only [split_ascii_whitespace, split_ascii_whitespace_aux, not_false_eq_true, not_sym, ↓reduceIte,
    List.nil_append, ne_eq, List.filter]
  split; rename_i gc; simp only [gc, Bool.not_true];
  simp only [ne_eq] at ind; split ;
  simp only [singleton_append, foldl_cons, append_eq, List.append_nil] ; exact ind
  unfold split_ascii_whitespace at ind; exact ind
  rename_i gc; simp only [gc, Bool.not_false]; rw[sub_split_ascii_whitespace_flatten1]
  simp only [ind, true_and]; intro x gx
  have gx:= sub_split_ascii_whitespace_flatten2 gx
  simp only [not_false_eq_true, not_sym, ne_eq, or_true, forall_true_left] at gx
  exact gx

lemma split_ascii_whitespace_flatten: flatten (split_ascii_whitespace s) = List.filter (fun a => ! is_ascii_whitespace a) s := by
  unfold split_ascii_whitespace; simp only [sub_split_ascii_whitespace_flatten]

lemma split_ascii_whitespace_not_contail_nil:  ∀ x ∈ split_ascii_whitespace s, x ≠ [] := by
  have i:= @sub_split_ascii_whitespace_flatten s true
  exact i.right

--#eval split_ascii_whitespace "    ".data

/-
Function: split_whitespace
From: str::core::split_whitespace
Description: https://doc.rust-lang.org/std/primitive.str.html#method.split_whitespace
-/

def split_whitespace_aux (s: Str) (w: Str) (prespace: Bool): List Str := match s with
  | [] => if prespace = false then [w] else []
  | h::t => if is_whitespace h then
          if prespace = false then w::split_whitespace_aux t [] true else split_whitespace_aux t []  true
          else split_whitespace_aux t (w++[h]) false

def split_whitespace (s: Str) := split_whitespace_aux s [] true

def split_whitespace_def (s: Str) := filter (fun sa: Str => sa.length > 0) (split_char_filter s is_whitespace)

--#eval split_whitespace "   abc  fsdf  f  ".data
--#eval split_whitespace "   ".data
--#eval split_whitespace_def "   abc  fsdf  f  ".data


lemma split_whitespace_aux_false_para1_append: split_whitespace_aux s w false = hs::ts →  split_whitespace_aux s (v++w) false = (v++hs)::ts:=by
  induction s generalizing w v
  unfold split_whitespace_aux
  split; simp only [cons.injEq, append_cancel_left_eq, imp_self];
  simp only [↓reduceIte, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rename_i h t ind
  unfold split_whitespace_aux
  split; simp only [↓reduceIte, cons.injEq, append_cancel_left_eq, imp_self]
  have : v ++ w ++ [h] = v ++ (w ++ [h]) :=by simp only [List.append_assoc]
  rw[this]; exact ind

lemma split_whitespace_aux_false_ne_nil  : split_whitespace_aux s w false ≠ [] := by
  induction s generalizing w
  simp only [split_whitespace_aux, ↓reduceIte, ne_eq, not_false_eq_true, not_sym]
  rename_i h t ind
  simp only [split_whitespace_aux, ↓reduceIte, ne_eq]
  split; simp only [not_false_eq_true]; exact ind

lemma split_whitespace_aux_para2_elim_case1: (¬ is_whitespace a) → split_whitespace_aux (a::s) w false = split_whitespace_aux (a::s) w true := by
  intro g; unfold split_whitespace_aux
  simp only [g, not_false_eq_true, not_sym, ↓reduceIte]

lemma split_whitespace_aux_para2_elim_case2: (is_whitespace a) → split_whitespace_aux (a::s) w false = w::split_whitespace_aux (a::s) w true := by
  intro g; unfold split_whitespace_aux
  simp only [g, not_false_eq_true, not_sym, ↓reduceIte]

theorem split_whitespace_EQ: split_whitespace s = split_whitespace_def s := by
  induction s
  unfold split_whitespace split_whitespace_aux split_whitespace_def split_char_filter split_char_filter_aux
  simp only [not_false_eq_true, not_sym, ↓reduceIte, gt_iff_lt, decide_False, filter_cons_of_neg,
    filter_nil]
  unfold filter; simp only [length_nil, lt_self_iff_false, decide_False, filter_nil]
  rename_i h t ind
  by_cases (is_whitespace h) ; rename_i gc;
  have e1: split_whitespace (h :: t) =  split_whitespace t:= by
    simp only [split_whitespace, split_whitespace_aux, gc, ↓reduceIte, not_false_eq_true, not_sym]
  unfold split_whitespace_def split_char_filter split_char_filter_aux
  simp only [gt_iff_lt, gc, ↓reduceIte, decide_False, not_false_eq_true, not_sym,
    filter_cons_of_neg]
  unfold filter; simp only [length_nil, lt_self_iff_false, decide_False]
  rw[← split_char_filter, ← split_whitespace_def, e1, ind]
  rename_i gc; unfold split_whitespace_def split_char_filter split_char_filter_aux
  simp only [gt_iff_lt, gc, not_false_eq_true, not_sym, ↓reduceIte, List.nil_append]
  generalize gsp1: split_char_filter_aux t is_whitespace [] = sp1
  cases sp1; simp only [split_char_filter_aux_ne_nil, not_false_eq_true, not_sym] at gsp1
  rename_i hsp1 tsp1; have gsp11:= @split_char_filter_aux_para1_append _ _ _ _ _ [h] gsp1
  simp only [singleton_append] at gsp11; rw[gsp11]
  simp only [length_cons, zero_lt_succ, decide_True, filter_cons_of_pos]
  unfold split_whitespace split_whitespace_aux
  simp only [gc, not_false_eq_true, not_sym, ↓reduceIte, List.nil_append]
  generalize gsp2: split_whitespace_aux t [] false = sp2
  cases sp2; simp only [split_whitespace_aux_false_ne_nil, not_false_eq_true, not_sym] at gsp2
  rename_i hsp2 tsp2; have gsp21:= @split_whitespace_aux_false_para1_append _ _ _ _  [h] gsp2
  simp only [singleton_append] at gsp21; rw[gsp21]
  unfold split_whitespace split_whitespace_def split_char_filter at ind
  rw[gsp1] at ind
  cases t; simp [split_char_filter_aux] at gsp1; simp only [split_whitespace_aux, ↓reduceIte, cons.injEq] at gsp2
  rw[← gsp1.left, ← gsp1.right, ← gsp2.right, ← gsp2.left]; simp only [filter_nil]
  rename_i ht tt
  by_cases (is_whitespace ht); rename_i gc; rw[split_whitespace_aux_para2_elim_case2 gc] at gsp2
  simp only [cons.injEq, true_and] at gsp2; rw[gsp2.right] at ind; rw[← gsp2.left, ind]
  simp only [split_char_filter_aux, gc, ↓reduceIte, cons.injEq] at gsp1; rw[← gsp1.left]
  simp only [gt_iff_lt, decide_False, not_false_eq_true, not_sym, filter_cons_of_neg]
  generalize gm: filter (fun a => decide (a.length > 0)) ([] :: tsp1) = m
  unfold filter at gm; simp only [length_nil, gt_iff_lt, lt_self_iff_false, decide_False] at gm; rw[gm]
  rename_i gc; rw[split_whitespace_aux_para2_elim_case1 gc] at gsp2; rw[gsp2] at ind
  have gc: hsp1.length > 0 := length_pos_from_not_nil.mp (split_char_filter_aux_head_ne_nil gc gsp1)
  unfold filter at ind; simp only [gt_iff_lt, gc, decide_True, cons.injEq] at ind
  simp only [ind]


lemma sub_split_whitespace_flatten1: List.foldl List.append [] (split_whitespace_aux s (v::tv) false)
        = v::List.foldl List.append [] (split_whitespace_aux s tv false) :=by
  induction s generalizing v tv
  simp only [split_whitespace_aux, ↓reduceIte, List.nil_append, foldl_cons, append_eq, foldl_nil,
    cons.injEq, true_and, split_whitespace]
  rename_i h t ind
  simp only [split_whitespace_aux, ↓reduceIte, List.nil_append, singleton_append, split_whitespace,
    not_false_eq_true, not_sym]
  split;
  simp only [singleton_append, foldl_cons, append_eq, List.nil_append]
  rw[fold_append_cons]; exact ind

lemma sub_split_whitespace_flatten2  (g: m ∈ split_whitespace_aux s w b ) (gc: b = true ∨ w ≠ [])
  :  ¬ m = [] :=by
  induction s generalizing w b
  simp only [split_whitespace_aux, List.nil_append] at g
  cases gc; rename_i gc; simp only [gc, not_false_eq_true, not_sym, ↓reduceIte, not_mem_nil] at g
  split at g; simp only [mem_singleton] at g; simp only [g]; assumption; simp only [not_mem_nil] at g
  rename_i h t ind
  simp only [split_whitespace_aux, List.nil_append] at g; split at g
  split at g;
  simp only [singleton_append, mem_cons] at g;
  rename_i gb; simp only [gb, not_false_eq_true, not_sym, ne_eq, false_or] at gc
  cases g; rename_i gw; rw[gw]; exact gc; rename_i g
  have ind:=ind g; simp only [ne_eq, not_true_eq_false, or_false, forall_true_left] at ind; exact ind
  have ind:=ind g; simp only [ne_eq, not_true_eq_false, or_false, forall_true_left] at ind; exact ind
  have ind:=ind g;simp only [not_false_eq_true, not_sym, ne_eq, append_eq_nil, and_false, or_true,
    forall_true_left] at ind; exact ind


lemma sub_split_whitespace_flatten: ((flatten (split_whitespace_aux s [] b) = List.filter (fun c => ! is_whitespace c) s))
                                  ∧ (∀ x ∈ split_whitespace s, x ≠ []):=by
  unfold flatten
  induction s generalizing b
  simp only [split_whitespace, split_whitespace_aux, not_false_eq_true, not_sym, ↓reduceIte,
    foldl_nil, filter_nil, not_mem_nil, ne_eq, IsEmpty.forall_iff, forall_const, and_self]
  split; simp only [List.nil_append, foldl_cons, append_eq, List.append_nil, foldl_nil, and_self]
  simp only [foldl_nil, and_self]
  rename_i h t ind
  simp only [split_whitespace, split_whitespace_aux, not_false_eq_true, not_sym, ↓reduceIte,
    List.nil_append, ne_eq, List.filter]
  split; rename_i gc; simp only [gc, Bool.not_true];
  simp only [ne_eq] at ind; split ;
  simp only [singleton_append, foldl_cons, append_eq, List.append_nil] ; exact ind
  unfold split_whitespace at ind; exact ind
  rename_i gc; simp only [gc, Bool.not_false]; rw[sub_split_whitespace_flatten1]
  simp only [ind, true_and]; intro x gx
  have gx:= sub_split_whitespace_flatten2 gx
  simp only [not_false_eq_true, not_sym, ne_eq, or_true, forall_true_left] at gx
  exact gx

lemma split_whitespace_flatten: flatten (split_whitespace s) = List.filter (fun c => ! is_whitespace c) s := by
  unfold split_whitespace; simp only [sub_split_whitespace_flatten]

lemma split_whitespace_not_contail_nil:  ∀ x ∈ split_whitespace s, x ≠ [] := by
  have g:= @sub_split_whitespace_flatten s true
  exact g.right

--#eval split_whitespace "    ".data



/-
Function: lines
From: str::core::lines
Description: https://doc.rust-lang.org/std/primitive.str.html#method.lines
-/

def lines (s: Str) := split s (Pattern.SingleChar '\n')

/-
Function: rust_matches
From: str::core::matches
Description: https://doc.rust-lang.org/std/primitive.str.html#method.matches
-/


lemma submatches_lem (g: substring_charIndex s ss = some p) (g1: ss.length > 0): s.length > 0:= by
  have h:= substring_charIndex_some_sound.mp g
  unfold is_first_substringcharIndex at h
  have h:= h.left; unfold is_substringcharIndex at h
  obtain⟨s0, s2, gs⟩ :=h; have gs:= gs.left; rw[gs]
  simp only [List.append_assoc, length_append, gt_iff_lt, add_pos_iff, g1, true_or, or_true]


def matches_char_filter (s: Str) (f: Char → Bool)  := match s with
  | [] => []
  | h::t => if f h then [h]::matches_char_filter t f else matches_char_filter t f

def matches_char_filter_def (s: Str) (f: Char → Bool) := List.map (fun x: Char => [x]) (List.filter f s)

theorem matches_char_filter_EQ : matches_char_filter s f = matches_char_filter_def s f :=by
  unfold matches_char_filter_def
  induction s
  simp only [matches_char_filter, filter_nil, map_nil]
  rename_i h t ind
  simp only [matches_char_filter, filter]
  split; rename_i gf; simp only [gf, map_cons, cons.injEq, true_and, ind]
  rename_i gf; simp only [ind, gf]

def matches_substring (s ss: Str) :=
  if _h: ss = [] then []
  else match _h1: substring_charIndex s ss with
    | none => []
    | some p => ss::(matches_substring (s.drop (p + ss.length)) ss)
termination_by length s
decreasing_by
  simp_wf;
  have i:  ss.length > 0 := by cases ss; contradiction; simp only [length_cons, gt_iff_lt, zero_lt_succ]
  have i2 := submatches_lem _h1 i
  omega

--List of n strings s
def list_Str_repeat (s: Str) (n: Nat) := match n with
  | 0 => []
  | succ m => s:: list_Str_repeat s m

theorem list_Str_repeat_length_sound: list_Str_repeat s n = l ↔ (l.length =n ∧ ∀ m ∈ l, m = s) :=by
  induction n generalizing l
  unfold list_Str_repeat; constructor
  intro g; simp only [← g, length_nil, not_mem_nil, false_implies, implies_true, and_self]
  intro g; symm; exact List.eq_nil_of_length_eq_zero g.left
  rename_i n ind
  simp only [list_Str_repeat]; constructor
  intro g; simp only [← g, length_cons, add_left_inj, mem_cons, forall_eq_or_imp, true_and]
  have ind:= @ind (list_Str_repeat s n); simp only [true_iff] at ind; exact ind
  intro g; cases l; simp only [length_nil, self_eq_add_left, add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, not_sym, not_mem_nil, false_implies, implies_true, and_true] at g
  rename_i ht tl; simp only [length_cons, add_left_inj, mem_cons, forall_eq_or_imp] at g
  have ind:= ind.mpr ⟨g.left, g.right.right⟩
  simp only [ind, cons.injEq, and_true]; symm; exact g.right.left

def matches_substring_def (s ss: Str) := list_Str_repeat ss (list_substring_charIndex s ss).length

theorem matches_substring_EQ (gss: ss.length > 0): matches_substring s ss = matches_substring_def s ss:= by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i l ind
  have gs11: ¬ ss = [] := by by_contra; rename_i gc; simp only [gc, length_nil, gt_iff_lt, lt_self_iff_false] at gss
  by_cases (l=0); rename_i gc; rw[gc] at gl
  have gl:=List.eq_nil_of_length_eq_zero gl; rw[gl]
  unfold matches_substring matches_substring_def list_Str_repeat list_substring_charIndex list_substring_charIndex_aux
  have : substring_charIndex [] ss = none := substring_charIndex_of_nil gss; rw[this]
  simp only [gs11, not_false_eq_true, not_sym, ↓reduceDIte, gt_iff_lt, gss, length_nil]
  unfold matches_substring matches_substring_def list_Str_repeat list_substring_charIndex list_substring_charIndex_aux
  simp only [gs11, not_false_eq_true, not_sym, ↓reduceDIte, gt_iff_lt, gss, zero_add]
  split ; simp only [length_nil]
  rename_i p _; simp only [length_cons, cons.injEq, true_and]
  rw[list_substring_charIndex_aux_para1_elim_mpr gss, length_map]
  generalize gs0: List.drop (p + ss.length) s = s0
  generalize gm: s0.length = m
  have id1: m < l := by rw[← gm, ← gl, ← gs0]; simp only [length_drop]; omega
  exact ind m id1 gm

--#eval matches_substring "abcXXXabcYYYabc".data "abc".data

def rust_matches (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => matches_char_filter s (fun x => x = c)
  | Pattern.ListChar l => matches_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => matches_char_filter s f
  | Pattern.WholeString ss => matches_substring s ss


/-
Function: rmatches
From: str::core::rmatches
Description: https://doc.rust-lang.org/std/primitive.str.html#method.rmatches
-/


def rmatches (s: Str) (P: Pattern) := List.reverse (rust_matches s P)


/-
Function: matches_indices
From: str::core::matches_indices
Description: https://doc.rust-lang.org/std/primitive.str.html#method.matches_indices
-/
def matches_indices_char_filter_aux (s: Str) (f: Char → Bool) (i: Nat):= match s with
  | [] => []
  | h::t => if f h then (i,[h])::matches_indices_char_filter_aux t f (i + Char.utf8Size h)
                    else  matches_indices_char_filter_aux t f (i + Char.utf8Size h)

def matches_indices_char_filter (s: Str) (f: Char → Bool) := matches_indices_char_filter_aux s f 0

def matches_indices_char_filter_def (s: Str) (f: Char → Bool) := List.zip (list_char_filter_pos s f) (matches_char_filter s f)

lemma matches_indices_char_filter_aux_EQ:
      matches_indices_char_filter_aux s f i = List.zip (list_char_filter_pos_aux s f i) (matches_char_filter s f):=by
  induction s generalizing i
  simp only [matches_indices_char_filter_aux, list_char_filter_pos_aux, zip_nil_left]
  rename_i h t ind
  simp only [matches_indices_char_filter_aux, list_char_filter_pos_aux, matches_char_filter]
  split; simp only [ind, zip_cons_cons]
  exact ind

lemma matches_indices_char_filter_EQ:
    matches_indices_char_filter s f = matches_indices_char_filter_def s f :=by
  unfold matches_indices_char_filter matches_indices_char_filter_def
  exact matches_indices_char_filter_aux_EQ

def matches_indices_substring_aux (s ss: Str) (k: Nat):=
  if _h: ss = [] then []
  else match _h1: substring_charIndex s ss with
    | none => []
    | some i => (k + byteSize (s.take i), ss)::(matches_indices_substring_aux (s.drop (i + ss.length)) ss (k + byteSize (s.take i) + byteSize ss ))
termination_by length s
decreasing_by
  simp_wf;
  have gk:  ss.length > 0 := by cases ss; contradiction; simp only [length_cons, gt_iff_lt, zero_lt_succ]
  have i2 := submatches_lem _h1 gk
  omega

def matches_indices_substring (s ss: Str) := matches_indices_substring_aux s ss 0

def matches_indices_substring_def (s ss: Str) := List.map (fun a => (a, ss)) (list_substring_pos s ss)

lemma matches_indices_substring_aux_EQ (gss: ss.length > 0):
      matches_indices_substring_aux s ss k = List.map (fun a => (a, ss)) (list_substring_pos_aux s ss k) :=by
  generalize gn: s.length = n
  induction n using Nat.strong_induction_on generalizing s k
  rename_i n ind
  have gs11: ¬ ss = [] := by by_contra; rename_i gc; simp only [gc, length_nil, gt_iff_lt, lt_self_iff_false] at gss
  by_cases (n=0); rename_i gc; rw[gc] at gn
  have gn:=List.eq_nil_of_length_eq_zero gn; rw[gn]
  unfold matches_indices_substring_aux list_substring_pos_aux
  simp only [gs11, not_false_eq_true, not_sym, ↓reduceDIte, drop_nil, take_nil, byteSize, add_zero,
    gt_iff_lt, gss]
  have : substring_charIndex [] ss = none := substring_charIndex_of_nil gss; rw[this]
  simp only [map_nil]
  unfold matches_indices_substring_aux list_substring_pos_aux
  simp only [gs11, not_false_eq_true, not_sym, ↓reduceDIte, gt_iff_lt, gss]
  split; simp only [map_nil]
  simp only [map_cons, cons.injEq, Prod.mk.injEq, add_right_inj, and_true]
  rename_i i _
  have : byteSize (take i s) = charIndex_to_pos s i := by rw[charIndex_to_pos_EQ, charIndex_to_pos_def]
  simp only [this, true_and]
  generalize gm: (drop (i + length ss) s).length = m
  have id1: m < n :=by
    rw[← gm, ← gn]; simp only [length_drop, tsub_lt_self_iff, add_pos_iff]; omega
  exact ind m id1 gm

theorem matches_indices_substring_EQ (gss: ss.length > 0):
      matches_indices_substring s ss = matches_indices_substring_def s ss :=by
  unfold matches_indices_substring matches_indices_substring_def list_substring_pos
  apply matches_indices_substring_aux_EQ gss

def matches_indices (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => matches_indices_char_filter s (fun x => x = c)
  | Pattern.ListChar l => matches_indices_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => matches_indices_char_filter s f
  | Pattern.WholeString ss => matches_indices_substring s ss

/-
Function: rmatches_indices
From: str::core::rmatches_indices
Description: https://doc.rust-lang.org/std/primitive.str.html#method.matches_indices
-/

def rmatches_indices (s: Str) (P: Pattern) := List.reverse (matches_indices s P)


/-
Function: starts_with
From: str::core::starts_with
Description: https://doc.rust-lang.org/std/primitive.str.html#method.starts_with
-/

def starts_with_char_filter (s: Str) (f: Char → Bool) := match s with | [] => false | h::_ => f h

lemma starts_with_char_filter_sound : starts_with_char_filter s f ↔  ∃ c t, f c ∧ s = c::t :=by
  cases s; simp only [starts_with_char_filter, not_false_eq_true, not_sym, and_false, exists_const,
    IsEmpty.forall_iff]
  rename_i h t; constructor
  intro g; simp only [starts_with_char_filter] at g; use h, t
  intro g; obtain ⟨c, t1, g⟩ :=g; simp only [cons.injEq] at g
  simp only [starts_with_char_filter, g]

def starts_with (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => starts_with_char_filter s (fun a => a == c)
  | Pattern.ListChar l => starts_with_char_filter s (fun a => a ∈ l)
  | Pattern.FilterFunction f => starts_with_char_filter s f
  | Pattern.WholeString ss => List.isPrefixOf ss s

lemma starts_with_substring_sound (gp: p = Pattern.WholeString ss): starts_with s p ↔ List.IsPrefix ss s := by
  rw[gp]; simp only [starts_with]; exact IsPrefix_isPrefixOf_EQ


lemma starts_with_char_filter_append : starts_with_char_filter (s1 ++ s2) f
                  = starts_with_char_filter (if s1 = [] then s2 else s1) f :=by
  cases s1; simp only [List.nil_append, ↓reduceIte]
  simp only [cons_append, not_false_eq_true, not_sym, ↓reduceIte]
  unfold starts_with_char_filter; simp only

/-
Function: ends_with
From: str::core::ends_with
Description: https://doc.rust-lang.org/std/primitive.str.html#method.ends_with
-/

def ends_with_char_filter (s: Str) (f: Char → Bool) := starts_with_char_filter s.reverse f

lemma ends_with_char_filter_sound : ends_with_char_filter s f ↔  ∃ c ss, f c ∧ s = ss ++ [c] :=by
  cases s; simp only [ends_with_char_filter, starts_with_char_filter, reverse_nil,
    not_false_eq_true, not_sym, nil_eq_append, and_false, exists_const, IsEmpty.forall_iff]
  rename_i h t; constructor
  intro g; simp [ends_with_char_filter, starts_with_char_filter] at g;
  split at g; contradiction
  rename_i h1 t1 g1; use h1, reverse t1
  simp only [g, true_and]
  have e1: reverse t1 ++ [h1] =  reverse (h1::t1) := by simp only [reverse_cons]
  have e2: h::t = reverse (reverse t ++ [h]) :=by simp only [reverse_append, reverse_cons,
    reverse_nil, List.nil_append, reverse_reverse, singleton_append]
  rw[e1,e2,g1];
  --mpr
  intro g; obtain ⟨c, t1, g⟩ :=g;
  simp only [ends_with_char_filter, starts_with_char_filter, g, reverse_append, reverse_cons,
    reverse_nil, List.nil_append, singleton_append]

def ends_with (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => ends_with_char_filter s (fun a => a == c)
  | Pattern.ListChar l => ends_with_char_filter s (fun a => a ∈ l)
  | Pattern.FilterFunction f => ends_with_char_filter s f
  | Pattern.WholeString ss => List.isSuffixOf ss s

lemma ends_with_substring_sound (gp: p = Pattern.WholeString ss): ends_with s p ↔  List.IsSuffix ss s := by
  rw[gp]; simp only [ends_with]; unfold List.isSuffixOf List.IsSuffix
  constructor
  intro g; have g:= IsPrefix_isPrefixOf_EQ.mp g ; unfold List.IsPrefix at g; obtain⟨t,g⟩:=g
  use reverse t; symm; have: s = s.reverse.reverse := by simp only [reverse_reverse]
  rw[this,← g]; simp only [reverse_append, reverse_reverse]
  intro g; obtain ⟨t, g⟩ := g
  rw[IsPrefix_isPrefixOf_EQ]; unfold List.IsPrefix; use reverse t; simp only [← g, reverse_append]

lemma ends_with_char_filter_append : ends_with_char_filter (s1 ++ s2) f
                  = ends_with_char_filter (if s2 = [] then s1 else s2) f :=by
  by_cases (s2 = []); rename_i gs2; rw[gs2]; simp only [List.append_nil, ↓reduceIte]
  rename_i gs2; simp only [ends_with_char_filter, reverse_append, starts_with_char_filter_append,
    reverse_eq_nil_iff, gs2, not_false_eq_true, not_sym, ↓reduceIte]

lemma append_partition_by_filter_unique (g1: s = a1 ++ b1) (g2: s = a2 ++ b2)
                  (g3: ¬ ends_with_char_filter a1 f) (g4: ¬ ends_with_char_filter a2 f)
                  (g5: ∀ m ∈ b1, f m )  (g6: ∀ m ∈ b2, f m ) : (a1 = a2) ∧ (b1 = b2) :=by
  rw [ends_with_char_filter_sound] at g3 g4
  simp only [exists_and_left, not_exists, not_and] at g3 g4
  have p1: List.IsPrefix a1 s := by simp only [g1, prefix_append]
  have p2: List.IsPrefix a2 s := by simp only [g2, prefix_append]
  by_cases (a1.length < a2.length); rename_i gl
  have gc:= List.prefix_of_prefix_length_le p1 p2 (by omega)
  unfold List.IsPrefix at gc; obtain ⟨t, gc⟩:=gc
  have i1: b1 = t ++ b2 := by
    rw[← gc, g1] at g2; simp only [List.append_assoc, append_cancel_left_eq] at g2; exact g2
  rw[i1] at g5; simp only [mem_append] at g5
  rw[← gc] at gl; simp only [length_append, lt_add_iff_pos_right] at gl
  have gt:= exist_last_mem gl; obtain ⟨ht,m,gt⟩:= gt
  have g5:= g5 m ; simp only [gt, mem_append, mem_singleton, or_true, true_or, forall_true_left] at g5
  have g4:= g4 m g5 (a1 ++ ht); rw[← gc, gt] at g4; simp only [List.append_assoc, not_true_eq_false] at g4
  by_cases (a1.length = a2.length) ; rename_i gc
  have i:= prefix_eq_of_length_eq p1 p2 gc ; rw[i, g2] at g1; simp only [append_cancel_left_eq] at g1; symm at g1; exact ⟨i, g1⟩
  have gl : a2.length < a1.length := by omega
  have gc:= List.prefix_of_prefix_length_le p2 p1 (by omega)
  unfold List.IsPrefix at gc; obtain ⟨t, gc⟩:=gc
  have i1: b2 = t ++ b1 := by
    rw[← gc, g2] at g1; simp only [List.append_assoc, append_cancel_left_eq] at g1; exact g1
  rw[i1] at g6; simp only [mem_append] at g6
  rw[← gc] at gl; simp only [length_append, lt_add_iff_pos_right] at gl
  have gt:= exist_last_mem gl; obtain ⟨ht,m,gt⟩:= gt
  have g6:= g6 m ; simp only [gt, mem_append, mem_singleton, or_true, true_or, forall_true_left] at g6
  have g3:= g3 m g6 (a2 ++ ht); rw[← gc, gt] at g3; simp only [List.append_assoc, not_true_eq_false] at g3


/-
Function: split_terminator
From: str::core::split_terminator
Description: https://doc.rust-lang.org/std/primitive.str.html#method.split_terminator
-/

def split_terminator (s: Str) (P: Pattern) := if ends_with s P then (split s P).dropLast else (split s P)

/-
Function: rsplit_terminator
From: str::core::rsplit_terminator
Description: https://doc.rust-lang.org/std/primitive.str.html#method.rsplit_terminator
-/

def rsplit_terminator (s: Str) (P: Pattern) := List.reverse (split_terminator s P)

/-
Function: rust_repeat
From: str::core::repeat
Description: https://doc.rust-lang.org/std/primitive.str.html#method.repeat
-/

def rust_repeat (s: Str) (n: Nat) := match n with
  | zero => []
  | succ t => s ++ rust_repeat s t

lemma repeat_succ : rust_repeat s (succ n) = (rust_repeat s n) ++ s := by
  induction n
  simp only [rust_repeat, List.append_nil, List.nil_append]
  rename_i n ind
  simp only [rust_repeat, List.append_assoc, append_cancel_left_eq] at *
  exact ind

lemma repeat_reverse : (rust_repeat s n).reverse = rust_repeat s.reverse n :=by
  induction n
  simp only [rust_repeat, reverse_nil]
  rename_i n ind
  rw[repeat_succ]; simp only [reverse_append]; simp only [ind, rust_repeat]

lemma repeat_add : rust_repeat s (m + n) = rust_repeat s m  ++ rust_repeat s n := by
  induction m
  simp only [zero_eq, zero_add, rust_repeat, List.nil_append]
  rename_i m ind
  have : succ m + n = succ (m + n) := by omega
  rw[this]; simp only [rust_repeat, List.append_assoc, append_cancel_left_eq]; exact ind

lemma repeat_length : (rust_repeat s n).length = n * s.length :=by
  induction n
  simp only [rust_repeat, length_nil, zero_eq, zero_mul]
  rename_i n ind
  simp only [rust_repeat, length_append]; rw[ind]
  have : s.length = 1 * s.length := by omega
  rw(config:={occs:=.pos [1]})[this]; rw[← Nat.add_mul];
  have : (1+n) = succ n :=by omega
  rw[this]


/-
Function: trim_start_matches
From: str::core::trim_start_matches
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_start_matches
-/

def trim_start_matches_char_filter (s: Str) (f: Char → Bool):= match s with
  | [] => []
  | h::t => if f h then trim_start_matches_char_filter t f else s

theorem trim_start_matches_char_filter_sound :(trim_start_matches_char_filter s f = tss) ↔  (¬ starts_with_char_filter tss f) ∧
                        (∃ pre, s = pre ++ tss ∧ (∀ c ∈ pre, f c) ) :=by
  induction s ;
  simp only [trim_start_matches_char_filter, Bool.not_eq_true, nil_eq_append]
  constructor; intro g; rw[← g]
  simp only [starts_with_char_filter, and_true, exists_eq_left, not_mem_nil, IsEmpty.forall_iff,
    forall_const, and_self]
  intro g; obtain ⟨_,g⟩:= g.right; simp only [g]
  rename_i h t ind
  simp only [trim_start_matches_char_filter, Bool.not_eq_true]
  split; simp only [Bool.not_eq_true] at ind;
  constructor; intro g; have ind:= ind.mp g;
  simp only [ind.left, true_and]
  obtain ⟨p, gp⟩:= ind.right; use h::p ; rename_i gh
  constructor; simp only [cons_append, cons.injEq, true_and]; exact gp.left
  simp only [mem_cons]; intro m gm
  cases gm; rename_i gm; simp only [gm, true_or, gh, forall_true_left]; assumption
  rename_i gm; exact gp.right m gm
  intro g; obtain ⟨p, gr⟩ := g.right
  cases p; simp only [List.nil_append, not_mem_nil, IsEmpty.forall_iff, and_true] at gr;
  rename_i gh; simp only [starts_with_char_filter, ← gr.left, gh, not_false_eq_true, not_sym, false_and] at g
  rename_i hp tp; simp only [cons_append, cons.injEq, mem_cons] at gr
  have id1: ∃ pre, t = pre ++ tss ∧ (∀ m ∈ pre, f m = true) := by
    simp only [gr, append_cancel_right_eq, exists_eq_left']
    intro m gi; simp only [gi, or_true, gr]
  exact ind.mpr ⟨g.left, id1⟩
  constructor; intro g; rename_i gh
  simp only [starts_with_char_filter, ← g, gh, true_and];
  use []; simp only [List.nil_append, not_mem_nil, IsEmpty.forall_iff, forall_const, and_self]
  intro g; rename_i gh; obtain ⟨p, gp⟩:= g.right;
  cases p; simp only [gp, List.nil_append];
  rename_i hp tp; simp only [cons_append, cons.injEq, mem_cons] at gp; rw[← gp.left.left] at gp
  have gp:= gp.right h; simp only [true_or, gh, not_false_eq_true, not_sym, forall_true_left] at gp

lemma length_pos_of_prefix_length_pos {s p: Str} (g1: List.isPrefixOf p s = true) (g2: p.length > 0) : s.length > 0 :=by
  by_contra
  have : s.length = 0 := by omega
  have g:= eq_nil_of_length_eq_zero this
  rw [g, IsPrefix_isPrefixOf_EQ] at g1; simp only [prefix_nil] at g1;
  simp only [g1, length_nil, gt_iff_lt, lt_self_iff_false] at g2

def trim_start_matches_substring (s: Str) (ss: Str):=
  if ss.length > 0 then
    if List.isPrefixOf ss s then trim_start_matches_substring (s.drop (ss.length)) ss else s
    else s
termination_by length s
decreasing_by simp_wf; rename_i g2 g1; have := length_pos_of_prefix_length_pos g1 g2; omega

theorem trim_start_matches_substring_sound (gss: ss.length>0):(trim_start_matches_substring s ss = trss) ↔  (¬ List.IsPrefix ss trss) ∧
                        (∃ n, s = (rust_repeat ss n) ++ trss ) :=by
  generalize gls: s.length = ls
  induction ls using Nat.strong_induction_on generalizing s trss
  rename_i ls ind
  by_cases (ls = 0); rename_i g1; rw[g1] at gls
  have gls:= List.eq_nil_of_length_eq_zero gls; rw[gls];
  unfold trim_start_matches_substring;
  simp only [gt_iff_lt, gss, ↓reduceIte, drop_nil, nil_eq_append, exists_and_right]
  have : ¬ List.isPrefixOf ss [] = true := by
    by_contra; rename_i gc; rw[IsPrefix_isPrefixOf_EQ] at gc; unfold List.IsPrefix at gc
    simp only [append_eq_nil, exists_eq_right] at gc;
    simp only [gc, length_nil, gt_iff_lt, lt_self_iff_false] at gss
  simp only [this, not_false_eq_true, not_sym, ↓reduceIte]
  constructor; intro g;
  simp only [← g, prefix_nil, ne_eq, length_pos_from_not_nil, gt_iff_lt, gss,
    not_sym, not_false_eq_true, and_true, true_and]
  use 0; simp only [rust_repeat]
  intro g; symm; exact g.right.right
  unfold trim_start_matches_substring
  simp only [gt_iff_lt, gss, ↓reduceIte]
  split
  generalize gm: (List.drop ss.length s).length = m
  have id1: m < ls:= by rw[← gm, ← gls]; simp only [length_drop]; omega
  rw[(ind m id1 gm)];
  constructor;
  intro g; simp only [g, not_false_eq_true, true_and];  obtain⟨n, g⟩:= g.right
  rename_i g1 _; rw[IsPrefix_isPrefixOf_EQ] at g1;
  use succ n ; rw[prefix_append_drop g1, g, rust_repeat, List.append_assoc]
  intro g; simp only [g, not_false_eq_true, true_and]; have gl:= g.left;  obtain⟨n, g⟩:= g.right
  rename_i g1 _; rw[IsPrefix_isPrefixOf_EQ] at g1;
  rw[prefix_append_drop g1] at g
  cases n; simp only [rust_repeat, List.nil_append] at g
  have : List.IsPrefix ss trss := by simp only [← g, prefix_append]
  contradiction
  rename_i n ; simp only [rust_repeat, List.append_assoc, append_cancel_left_eq] at g; use n
  constructor;
  intro g; rename_i g1; rw[IsPrefix_isPrefixOf_EQ] at g1;
  simp only [← g, g1, not_false_eq_true, true_and]; use 0; simp only [rust_repeat,List.nil_append]
  intro g; obtain⟨n, g⟩:= g.right;
  cases n; simp only [rust_repeat, List.nil_append] at g; exact g
  rename_i n; rw[rust_repeat, List.append_assoc] at g; rename_i g1 _; rw[IsPrefix_isPrefixOf_EQ] at g1;
  have : List.IsPrefix ss s := by simp only [g, prefix_append]
  contradiction



def trim_start_matches (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => trim_start_matches_char_filter s (fun a => a == c)
  | Pattern.ListChar l => trim_start_matches_char_filter s (fun a => a ∈ l)
  | Pattern.FilterFunction f => trim_start_matches_char_filter s f
  | Pattern.WholeString ss => trim_start_matches_substring s ss

/-
Function: trim_end_matches
From: str::core::trim_end_matches
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_end_matches
-/

def trim_end_matches_char_filter (s: Str) (f: Char → Bool):= List.reverse (trim_start_matches_char_filter (List.reverse s) f)

theorem trim_end_matches_char_filter_sound : (trim_end_matches_char_filter s f = tes) ↔ (¬ ends_with_char_filter tes f) ∧
               (∃ suf, s = tes ++ suf ∧ (∀ c ∈ suf, f c) ) :=by
  simp only [ends_with_char_filter, trim_end_matches_char_filter, reverse_cons, reverse_reverse, Bool.not_eq_true]
  constructor; intro g
  have e1: trim_start_matches_char_filter (reverse s) f = reverse tes := by simp only [← g, reverse_reverse]
  rw[trim_start_matches_char_filter_sound] at e1; simp only [e1, true_and]; obtain⟨p,gp⟩:=e1.right
  use reverse p;
  have : s = s.reverse.reverse := by simp only [reverse_reverse];
  rw(config:={occs:=.pos [1]})[this, gp.left];
  simp only [reverse_append, reverse_reverse, mem_reverse, true_and]; exact gp.right
  intro g
  have : ∃ pre, reverse s = pre ++ reverse tes ∧ (∀ m ∈ pre, f m):= by
    obtain⟨p,gp⟩:=g.right; use reverse p
    simp only [gp, reverse_append, mem_reverse, true_and]; exact gp.right
  have : trim_start_matches_char_filter (reverse s) f = reverse tes :=by
    apply trim_start_matches_char_filter_sound.mpr; simp only [g, not_false_eq_true, not_sym, this, and_self]
  simp only [this, reverse_reverse]

def trim_end_matches_substring (s: Str) (ss: Str):= List.reverse (trim_start_matches_substring s.reverse ss.reverse)

lemma sub_trim_end_matches_substring_sound: ∀ n, (s = tes ++ rust_repeat s1 n ↔ s.reverse = rust_repeat s1.reverse n ++ tes.reverse) :=by
  intro n; constructor; intro g; rw[g]; simp only [reverse_append, append_cancel_right_eq]; exact repeat_reverse
  intro g; rw[← repeat_reverse, reverse_iif] at g; simp only [reverse_reverse, reverse_append] at g; exact g

theorem trim_end_matches_substring_sound (gss: ss.length>0) :(trim_end_matches_substring s ss = tes) ↔  (¬ List.IsSuffix ss tes) ∧
                        (∃ n, s = tes ++ (rust_repeat ss n)) :=by
  have gss: ss.reverse.length > 0 :=by simp only [length_reverse, gt_iff_lt]; exact gss
  simp only [trim_end_matches_substring]; rw[reverse_change_side]
  rw(config:={occs:=.pos [2]})[← @reverse_reverse _ ss, ← @reverse_reverse _ tes]
  rw[List.reverse_suffix, exists_EQ sub_trim_end_matches_substring_sound]
  exact trim_start_matches_substring_sound gss ;


def trim_end_matches (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => trim_end_matches_char_filter s (fun a => a == c)
  | Pattern.ListChar l => trim_end_matches_char_filter s (fun a => a ∈ l)
  | Pattern.FilterFunction f => trim_end_matches_char_filter s f
  | Pattern.WholeString ss => trim_end_matches_substring s ss

/-
Function: trim_matches
From: str::core::trim_matches
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_matches
-/
--NOTE THAT: trim_matches will return an error if the input pattern is a WholeString

def trim_matches_char_filter (s: Str) (f: Char → Bool):= trim_start_matches_char_filter (trim_end_matches_char_filter s f) f


lemma sub_trim_matches_char_filter_sound1 : ¬ ends_with_char_filter s f →   ¬ ends_with_char_filter (trim_start_matches_char_filter s f) f:= by
  induction s ; simp only [ends_with_char_filter, reverse_nil, Bool.not_eq_true, trim_start_matches_char_filter,imp_self]
  rename_i h t ind
  simp only [ends_with_char_filter, reverse_cons, Bool.not_eq_true, trim_start_matches_char_filter]
  split; rw[← ends_with_char_filter, starts_with_char_filter_append]; rename_i gh
  split; simp only [starts_with_char_filter, gh, not_false_eq_true, not_sym, IsEmpty.forall_iff]
  rw[← ends_with_char_filter]; simp only [Bool.not_eq_true] at ind; exact ind
  simp only [reverse_cons, imp_self]


theorem trim_matches_char_filter_sound :(trim_matches_char_filter s f = trs) ↔ ¬ starts_with_char_filter trs f ∧ ¬ ends_with_char_filter trs f ∧
            (∃ pre suf, s = pre ++ trs ++ suf ∧ (∀ c ∈ pre, f c) ∧ (∀ c ∈ suf, f c) ):= by
  unfold trim_matches_char_filter;
  generalize gt: trim_end_matches_char_filter s f = tes; rw[trim_end_matches_char_filter_sound] at gt;
  have i:= sub_trim_matches_char_filter_sound1 gt.left
  constructor; intro g; rw[g] at i
  rw[trim_start_matches_char_filter_sound] at g;
  simp only [g.left, not_false_eq_true, not_sym, i, List.append_assoc, true_and]
  obtain ⟨p, gp⟩ := g.right; obtain ⟨t,gt⟩:=gt.right
  use p, t; simp only [gt, gp, List.append_assoc, true_and]; exact ⟨gp.right, gt.right⟩
  --mpr
  intro g; rw[trim_start_matches_char_filter_sound]; simp only [g, not_false_eq_true, not_sym, true_and]
  obtain ⟨p,t,g⟩ := g.right.right; obtain ⟨t1,gt⟩:=gt.right
  rename_i gtes _ ; have gtes:= gtes.left;
  by_cases (trs = []) ; rename_i gc
  have gms: ∀ m ∈ s, f m = true := by
    simp only [g, gc, List.append_nil, mem_append]
    intro m gm; cases gm; rename_i gm; exact g.right.left m gm;
    rename_i gm; exact g.right.right m gm;
  rw[gt.left] at gms; simp only [mem_append] at gms
  have : tes = [] := by
    by_contra; rename_i gt
    have gm:= exist_last_mem (length_pos_from_not_nil.mp gt); obtain ⟨htes, m, gm⟩:= gm
    have gms:=gms m;
    simp only [gm, mem_append, mem_singleton, or_true, true_or, forall_true_left] at gms
    rw[gm] at gtes;
    simp only [ends_with_char_filter, starts_with_char_filter, reverse_append, reverse_cons,
      reverse_nil, List.nil_append, singleton_append, gms, not_true_eq_false] at gtes
  simp only [this, gc, List.append_nil, exists_eq_left', not_mem_nil, IsEmpty.forall_iff, forall_const]
  have i: ¬ends_with_char_filter (p ++ trs) f  := by
    rw[ends_with_char_filter_append]; rename_i gc;
    simp only [gc, not_false_eq_true, not_sym, ↓reduceIte, Bool.not_eq_true]
    rename_i g0; simp only [g0]
  have gx:= append_partition_by_filter_unique gt.left g.left gtes i gt.right g.right.right
  use p; simp only [gx, true_and]; exact g.right.left



def trim_matches (s: Str) (P: Pattern) : Option Str := match P with
  | Pattern.SingleChar c => some (trim_matches_char_filter s (fun a => a == c))
  | Pattern.ListChar l => some (trim_matches_char_filter s (fun a => a ∈ l))
  | Pattern.FilterFunction f => some (trim_matches_char_filter s f)
  | Pattern.WholeString _ => none

/-
Function: trim_ascii_start
From: str::core::trim_ascii_start
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii_start
-/

def trim_ascii_start (s: Str) := trim_start_matches_char_filter s is_ascii_whitespace

/-
Function: trim_ascii_end
From: str::core::trim_ascii_end
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii_end
-/

def trim_ascii_end (s: Str) := trim_end_matches_char_filter s is_ascii_whitespace


/-
Function: trim_ascii
From: str::core::trim_ascii
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii
-/


def trim_ascii (s: Str) := trim_ascii_start (trim_ascii_end s)

/-
Function: trim_ascii_start
From: str::core::trim_ascii_start
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii_start
-/

def trim_start (s: Str) := trim_start_matches_char_filter s is_whitespace

/-
Function: trim_ascii_end
From: str::core::trim_ascii_end
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii_end
-/

def trim_end (s: Str) := trim_end_matches_char_filter s is_whitespace


/-
Function: trim_ascii
From: str::core::trim_ascii
Description: https://doc.rust-lang.org/std/primitive.str.html#method.trim_ascii
-/


def trim (s: Str) := trim_start (trim_end s)


/-
Function: replace
From: str::core::replace
Description: https://doc.rust-lang.org/std/primitive.str.html#method.replace
-/


def replace_substring (s ss sr: Str) :=
  if _h: ss.length > 0 then
    match _t: substring_charIndex s ss with
      | none => s
      | some i => (s.take i) ++ sr ++ (replace_substring (s.drop (i + ss.length)) ss sr)
  else s
termination_by length s
decreasing_by simp_wf; have:= substring_charIndex_terminate _t _h; simp only [_h, or_true, and_true,
  gt_iff_lt]; omega

def replace_substring_def (s ss sr: Str) := str_concat_pad (split_substring s ss) sr

theorem replace_substring_EQ (gss: ss.length > 0)
      : replace_substring s ss sr = replace_substring_def s ss sr :=by
  unfold replace_substring_def
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s
  rename_i l ind
  have gs11: ¬ ss = [] := by by_contra; rename_i gc; simp only [gc, length_nil, gt_iff_lt, lt_self_iff_false] at gss
  by_cases (l=0); rename_i gc; rw[gc] at gl
  have gl:=List.eq_nil_of_length_eq_zero gl; rw[gl]
  unfold split_substring replace_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte, List.nil_append, drop_nil, take_nil]
  have : substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[this]; simp only [drop_nil, take_nil, str_concat_pad];
  unfold split_substring  replace_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte, List.append_assoc, drop_drop]
  split; simp only [str_concat_pad]
  rename_i i _;
  simp only [str_concat_pad, List.append_assoc]
  have : split_substring (List.drop (i + ss.length) s) ss ≠  [] := split_substring_ne_nil
  simp only [str_concat_pad.match_1.eq_2, append_cancel_left_eq]
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < l := by rw[← gm, ← gl]; simp only [length_drop]; omega
  exact ind m id1 gm


--#eval replace_substring "this is old".data "is".data "an".data

def replace_char_filter (s: Str) (f: Char → Bool) (ss: Str) := match s with
  | [] => []
  | h::t => if f h then ss ++ (replace_char_filter t f ss) else h::(replace_char_filter t f ss)

def replace_char_filter_def (s: Str) (f: Char → Bool) (ss: Str) := str_concat_pad (split_char_filter s f) ss

lemma sub_replace_char_filter_EQ: str_concat_pad (split_char_filter_aux s f (w::u)) ss
                = w:: str_concat_pad (split_char_filter_aux s f u) ss :=by
  induction s generalizing w u
  simp only [str_concat_pad]
  rename_i h t ind
  simp only [split_char_filter_aux, List.nil_append, cons_append]
  split;
  have: split_char_filter_aux t f []  ≠ [] :=by rw[← split_char_filter]; exact split_char_filter_ne_nil
  simp only [str_concat_pad, append_eq, List.nil_append, str_concat_pad.match_1.eq_2, cons_append, List.append_assoc]
  exact ind

theorem replace_char_filter_EQ
      : replace_char_filter s f ss = replace_char_filter_def s f ss:=by
  unfold replace_char_filter_def
  induction s
  simp only [replace_char_filter, str_concat_pad]
  rename_i h t ind
  simp only [replace_char_filter, split_char_filter, split_char_filter_aux, List.nil_append]
  split; rw[ ← split_char_filter]
  simp only [str_concat_pad, append_eq, List.nil_append, split_char_filter_ne_nil,
    IsEmpty.forall_iff, str_concat_pad.match_1.eq_2, append_cancel_left_eq, ind]
  rw[sub_replace_char_filter_EQ,← split_char_filter, ind]


--#eval replace_char_filter "this is old".data Char.is_ascii_whitespace "XX".data

def replace (s: Str) (i: Pattern) (sr: Str):= match i with
  | Pattern.SingleChar c => replace_char_filter s (fun x => x = c) sr
  | Pattern.ListChar l => replace_char_filter s (fun x => x ∈ l) sr
  | Pattern.FilterFunction f => replace_char_filter s f sr
  | Pattern.WholeString ss => replace_substring s ss sr

/-
Function: replacen
From: str::core::replacen
Description: https://doc.rust-lang.org/std/primitive.str.html#method.replacen
-/

def replacen_substring (s ss sr: Str) (n: Nat):=
  if _h: ss.length > 0 then
    if n > 0 then
      match _t: substring_charIndex s ss with
        | none => s
        | some i => (s.take i) ++ sr ++ (replacen_substring (s.drop (i + ss.length)) ss sr (n-1))
    else s
  else s
termination_by length s
decreasing_by simp_wf; have:= substring_charIndex_terminate _t _h; simp only [_h, or_true, and_true,
  gt_iff_lt]; omega

def replacen_substring_def (s ss sr: Str) (n:Nat):= str_concat_pad (splitn_substring s (n+1) ss ) sr

theorem replacen_substring_EQ (gss: ss.length > 0)
      : replacen_substring s ss sr n= replacen_substring_def s ss sr n:=by
  unfold replacen_substring_def
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s n
  rename_i l ind
  have gs11: ¬ ss = [] := by by_contra; rename_i gc; simp only [gc, length_nil, gt_iff_lt, lt_self_iff_false] at gss
  by_cases (l=0); rename_i gc; rw[gc] at gl
  have gl:=List.eq_nil_of_length_eq_zero gl; rw[gl]
  unfold splitn_substring replacen_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte, List.nil_append, drop_nil, take_nil]
  have : substring_charIndex [] ss = none := substring_charIndex_of_nil gss
  rw[this]; simp only [drop_nil, take_nil, str_concat_pad];
  split; split; simp only [str_concat_pad]; split; simp only [str_concat_pad]; simp only [str_concat_pad]
  rename_i gn; simp only [not_lt, nonpos_iff_eq_zero] at gn; simp only [gn, ↓reduceIte, str_concat_pad]
  unfold splitn_substring  replacen_substring
  simp only [gt_iff_lt, gss, ↓reduceDIte, append_assoc, add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, not_sym, ↓reduceIte, add_left_eq_self, add_tsub_cancel_right]
  split; split; split; omega; simp only [str_concat_pad]; split; omega
  rename_i gn i _ _ ;
  have : splitn_substring (List.drop (i + ss.length) s) n ss  ≠ [] := splitn_substring_ne_nil gn
  simp only [str_concat_pad, append_assoc, append_cancel_left_eq]
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < l := by rw[← gm, ← gl]; simp only [length_drop]; omega
  have ind:= @ind m id1 _ (n-1) gm
  have: n - 1 + 1 = n :=by omega
  rw[this] at ind; exact ind
  rename_i gn; simp only [not_lt, nonpos_iff_eq_zero] at gn;
  simp only [gn, ↓reduceIte, str_concat_pad]


def replacen_char_filter (s: Str) (f: Char → Bool) (sr: Str) (n: Nat) :=
  if (n > 0) then
    match s with
      | [] => []
      | h::t => if f h then sr ++ (replacen_char_filter t f sr (n-1)) else h::(replacen_char_filter t f sr n)
  else s

def replacen_char_filter_def (s: Str) (f: Char → Bool) (sr: Str) (n: Nat) := str_concat_pad (splitn_char_filter s (n+1) f) sr

lemma sub_replacen_char_filter_EQ (gn: n > 0):  str_concat_pad (splitn_char_filter_aux s n f  (w::u) ) sr
                = w:: str_concat_pad (splitn_char_filter_aux s n f u ) sr :=by
  induction s generalizing w u n
  have gn: ¬ n = 0 := by omega
  simp only [splitn_char_filter_aux, gn, not_false_eq_true, not_sym, ↓reduceIte, append_nil,
    ite_self, str_concat_pad]
  rename_i h t ind
  have gn: ¬ n = 0 := by omega
  simp only [splitn_char_filter_aux, gn, not_false_eq_true, not_sym, ↓reduceIte, cons_append]
  split; simp only [str_concat_pad]; split
  have: splitn_char_filter_aux t (n-1) f []  ≠ [] :=by rw[← splitn_char_filter]; exact splitn_char_filter_ne_nil (by omega)
  simp only [str_concat_pad, append_eq, List.nil_append, str_concat_pad.match_1.eq_2, cons_append, List.append_assoc]
  exact ind (by assumption)

theorem replacen_char_filter_EQ
      : replacen_char_filter s f sr n = replacen_char_filter_def s f sr n:=by
  unfold replacen_char_filter_def
  induction s generalizing n
  simp only [replacen_char_filter, gt_iff_lt, ite_self, splitn_char_filter, splitn_char_filter_aux,
    add_eq_zero, one_ne_zero, and_false, not_false_eq_true, not_sym, ↓reduceIte, add_left_eq_self,
    append_nil, str_concat_pad]
  rename_i h t ind
  simp only [replacen_char_filter, gt_iff_lt, splitn_char_filter, splitn_char_filter_aux,
    add_eq_zero, one_ne_zero, and_false, not_false_eq_true, not_sym, ↓reduceIte, add_left_eq_self,
    nil_append, add_tsub_cancel_right]
  split; have gn: ¬ n = 0 := by omega
  simp only [gn, not_false_eq_true, not_sym, ↓reduceIte]
  split; rw[ ← splitn_char_filter]
  have : splitn_char_filter t n f ≠ [] := splitn_char_filter_ne_nil (by assumption)
  have: n - 1 + 1 = n :=by omega
  simp only [str_concat_pad, append_eq, List.nil_append, split_char_filter_ne_nil,
    IsEmpty.forall_iff, str_concat_pad.match_1.eq_2, append_cancel_left_eq, ind, this]
  rw[sub_replacen_char_filter_EQ (by omega), ← splitn_char_filter, ind]
  rename_i gn; simp only [not_lt, nonpos_iff_eq_zero] at gn
  simp only [gn, ↓reduceIte, str_concat_pad]


def replacen (s: Str) (P: Pattern) (sr: Str) (n: Nat):= match P with
  | Pattern.SingleChar c => replacen_char_filter s (fun x => x = c) sr n
  | Pattern.ListChar l => replacen_char_filter s (fun x => x ∈ l) sr n
  | Pattern.FilterFunction f => replacen_char_filter s f sr n
  | Pattern.WholeString ss => replacen_substring s ss sr n

/-
Function: strip_prefix
From: str::core::strip_prefix
Description: https://doc.rust-lang.org/std/primitive.str.html#method.strip_prefix
-/

def strip_prefix_char_filter (s: Str) (f: Char → Bool) := match s with
  | [] => none
  | h::t => if f h then some t else none

theorem strip_prefix_char_filter_none_sound : strip_prefix_char_filter s f = none ↔ ¬ ∃ h t, s = h::t ∧ f h :=by
  unfold strip_prefix_char_filter; constructor
  split; simp only [not_false_eq_true, not_sym, false_and, exists_const, forall_true_left]
  split; simp only [cons.injEq, exists_and_right, exists_and_left, exists_eq', and_true,
    exists_eq_left', Bool.not_eq_true, IsEmpty.forall_iff]
  simp only [cons.injEq, exists_and_right, exists_and_left, exists_eq', and_true, exists_eq_left',
    Bool.not_eq_true, forall_true_left]
  rename_i g; simp only [Bool.not_eq_true] at g; exact g
  simp only [exists_and_right, not_exists, not_and, Bool.not_eq_true, forall_exists_index]
  intro g; split; simp only
  split; simp_all only [cons.injEq, and_imp, forall_apply_eq_imp_iff, forall_eq', not_false_eq_true,not_sym]
  simp only

theorem strip_prefix_char_filter_some_sound : strip_prefix_char_filter s f = some t ↔  ∃ h, s = h::t ∧ f h :=by
  unfold strip_prefix_char_filter; constructor
  split ; simp only [not_false_eq_true, not_sym, false_and, exists_const, IsEmpty.forall_iff]
  split; simp_all only [Option.some.injEq, cons.injEq, and_true, exists_eq_left', implies_true]
  simp only [cons.injEq, IsEmpty.forall_iff]
  split; simp only [not_false_eq_true, not_sym, false_and, exists_const, IsEmpty.forall_iff]
  split; simp_all only [cons.injEq, Option.some.injEq, forall_exists_index, and_imp, implies_true,
    forall_const]
  simp_all only [Bool.not_eq_true, cons.injEq, forall_exists_index, and_imp, imp_false, forall_eq',
    implies_true]


def strip_prefix_substring (s: Str) (p: Str) : Option Str := if List.isPrefixOf p s then some (s.drop p.length) else none

theorem strip_prefix_substring_none_sound : strip_prefix_substring s p = none ↔ ¬ List.IsPrefix p s :=by
  unfold strip_prefix_substring
  split; rw[← IsPrefix_isPrefixOf_EQ]; simp_all only [not_true_eq_false]
  rw[← IsPrefix_isPrefixOf_EQ]; simp_all only [Bool.not_eq_true, not_false_eq_true, not_sym]


theorem strip_prefix_substring_some_sound : strip_prefix_substring s p = some t ↔ List.IsPrefix p s ∧ s = p ++ t :=by
  unfold strip_prefix_substring; constructor
  split; rename_i g; rw[IsPrefix_isPrefixOf_EQ] at g;
  simp only [Option.some.injEq, g, true_and]
  intro g1; rw[← g1]; apply prefix_append_drop g
  simp only [IsEmpty.forall_iff]
  intro g; simp only [IsPrefix_isPrefixOf_EQ.mpr g.left, ↓reduceIte, Option.some.injEq]
  simp only [g, drop_left]


def strip_prefix (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => strip_prefix_char_filter s (fun x => x = c)
  | Pattern.ListChar l => strip_prefix_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => strip_prefix_char_filter s f
  | Pattern.WholeString s1 => strip_prefix_substring s s1


/-
Function: strip_suffix
From: str::core::strip_suffix
Description: https://doc.rust-lang.org/std/primitive.str.html#method.strip_suffix
-/


def strip_suffix_char_filter (s: Str) (f: Char → Bool) := match strip_prefix_char_filter s.reverse f with
  | none => none
  | some s1 => some (s1.reverse)

lemma sub_strip_suffix_char_filter_sound1: strip_suffix_char_filter s f = none ↔ strip_prefix_char_filter s.reverse f = none :=by
    unfold strip_suffix_char_filter; split; simp_all only
    simp_all only [not_false_eq_true, not_sym]

lemma sub_strip_suffix_char_filter_sound2 {f: Char→ Bool}: (∃ c t, s = t ++ [c] ∧ f c = true) ↔  ∃ c t, reverse s = c::t ∧ f c :=by
    constructor;
    intro g;  obtain ⟨c, t, g⟩:=g; use c, t.reverse ;
    simp only [g, reverse_append, reverse_cons, reverse_nil, List.nil_append, singleton_append, and_self]
    intro g;  obtain ⟨c, t, g⟩:=g; use c, t.reverse ;
    rw[reverse_iif]; simp only [g, reverse_append, reverse_cons, reverse_nil, List.nil_append,
      reverse_reverse, singleton_append, and_self]

theorem strip_suffix_char_filter_none_sound : strip_suffix_char_filter s f = none ↔ ¬ ∃ c t, s = t ++ [c] ∧ f c :=by
  rw[sub_strip_suffix_char_filter_sound1, sub_strip_suffix_char_filter_sound2]; exact strip_prefix_char_filter_none_sound

theorem strip_suffix_char_filter_some_sound : strip_suffix_char_filter s f = some t ↔  ∃ c, s = t ++ [c] ∧ f c :=by
  unfold strip_suffix_char_filter;
  split; simp only [not_false_eq_true, not_sym, false_iff,  not_and, Bool.not_eq_true]
  rename_i g; rw[← sub_strip_suffix_char_filter_sound1] at g;
  by_contra; rename_i g1; obtain ⟨c, g1⟩:= g1
  have gc : ∃ c t, s = t ++ [c] ∧ f c = true := by use c, t
  have := strip_suffix_char_filter_none_sound.mp g; contradiction
  rename_i u g; rw[strip_prefix_char_filter_some_sound] at g; obtain ⟨c, g⟩:=g;
  simp only [Option.some.injEq]; constructor
  intro gu; use c; rw[reverse_iif]; simp only [g, reverse_append, reverse_cons, reverse_nil,
    List.nil_append, singleton_append, cons.injEq, true_and, and_true]
  exact reverse_change_side.mp gu
  simp only [reverse_change_side, reverse_cons] at g
  intro g1; obtain ⟨c0, g1⟩:=g1; simp only [g] at g1
  rw [reverse_iif] at g1;
  simp only [reverse_append, reverse_cons, reverse_nil, List.nil_append,
    reverse_reverse, singleton_append, cons.injEq] at g1
  exact reverse_change_side.mpr g1.left.right


def strip_suffix_substring (s: Str) (p: Str) : Option Str := if List.isSuffixOf p s then some (s.take (s.length - p.length)) else none

def strip_suffix (s: Str) (P: Pattern) := match P with
  | Pattern.SingleChar c => strip_suffix_char_filter s (fun x => x = c)
  | Pattern.ListChar l => strip_suffix_char_filter s (fun x => x ∈ l)
  | Pattern.FilterFunction f => strip_suffix_char_filter s f
  | Pattern.WholeString ss => strip_suffix_substring s ss

theorem strip_suffix_substring_none_sound : strip_suffix_substring s p = none ↔ ¬ List.IsSuffix p s :=by
  unfold strip_suffix_substring
  split; rw[← IsSuffix_isSuffixOf_EQ]; simp_all only [not_true_eq_false]
  rw[← IsSuffix_isSuffixOf_EQ]; simp_all only [Bool.not_eq_true, not_false_eq_true, not_sym]

theorem strip_suffix_substring_some_sound : strip_suffix_substring s p = some t ↔ List.IsSuffix p s ∧ s = t ++ p :=by
  unfold strip_suffix_substring; constructor
  split; rename_i g; rw[IsSuffix_isSuffixOf_EQ] at g;
  simp only [Option.some.injEq, g, true_and]
  intro g1; rw[← g1]; apply take_append_suffix g
  simp only [IsEmpty.forall_iff]
  intro g; simp only [IsSuffix_isSuffixOf_EQ.mpr g.left, ↓reduceIte, Option.some.injEq]
  simp only [g, length_append, add_tsub_cancel_right, take_left]

/-
Function: to_ascii_lowercase
From: str::core::to_ascii_lowercase
Description: https://doc.rust-lang.org/std/primitive.str.html#method.to_ascii_lowercase
-/

def to_ascii_lowercase (s: Str) := List.map Char.toLower s

/-
Function: to_ascii_uppercase
From: str::core::to_ascii_uppercase
Description: https://doc.rust-lang.org/std/primitive.str.html#method.to_ascii_uppercase
-/

def to_ascii_uppercase (s: Str) := List.map Char.toUpper s

/-
Function: is_ascii
From: str::core::is_ascii
Description: https://doc.rust-lang.org/std/primitive.str.html#method.is_ascii
-/

def is_ascii (s: Str) := List.all s Char_is_ascii

/-
Function: eq_ignore_ascii_case
From: str::core::eq_ignore_ascii_case
Description: https://doc.rust-lang.org/std/primitive.str.html#method.eq_ignore_ascii_case
-/

def eq_ignore_ascii_case (s1 s2: Str):= (to_ascii_lowercase s1 = to_ascii_lowercase s2)


end RustString
