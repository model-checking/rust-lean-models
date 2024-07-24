-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
import RustLeanModels.Basic
import Lean
open Char
open List
open Mathlib
open Nat
set_option maxHeartbeats 10000000


--TODO: prove the axiom from utf8EncodeChar function in Data/String/Extra.lean
opaque toByte : (Char ×  Nat) →  Nat

def isValid_toByte_input (u : Char ×  Nat) : Bool := u.2 < utf8Size u.1

/-
The following three axioms are stated according to the description of UTF8 encoding
Source: https://en.wikipedia.org/wiki/UTF-8#:~:text=UTF%2D8%20is%20a%20variable,Unicode%20Standard

Axiom "Char_firstbyte_ne_others" is based on the fact that only the first bytes of all characters
start with '0' or '11', while all other bytes start with '10'. In other words, the values of the
first bytes of all characters are outside of the range [128, 191], while the value of other bytes
are inside of the range.

Axiom "Char_size_eq_of_firstbyte_eq" is based on the fact that the number of bytes used to encode
a character is determined by its first byte. Specifically, if the first byte starts with '0',
'11', '111', '1111', then the number of bytes is 1, 2, 3, 4 accordingly.

Axiom "exists_byte_ne_of_Chat_ne" is based on the fact that if two characters are not equal, then
at some (byte) position in their encoding, the two corresponding bytes are different.
-/

axiom Char_firstbyte_ne_others {c1 c2: Char} {i: Nat}:  i ≠ 0 → toByte (c1,0) ≠ toByte (c2,i)

axiom Char_size_eq_of_firstbyte_eq {c1 c2: Char}: toByte (c1,0) = toByte (c2,0) →  utf8Size c1 = utf8Size c2

axiom exists_byte_ne_of_Chat_ne {c1 c2: Char} : c1 ≠ c2 → ∃ i , i < utf8Size c1 ∧  toByte (c1,i) ≠ toByte (c2,i)


/-
The Char_toUTF8 function converts a Char into it UTF8 encoding.
Char_toUTF8 is the same as String.utf8EncodeChar, but it is defined based on the opaque function toByte,
so we can perform reasoning on it through the axioms.
-/
def Char_toUTF8_aux (c : Char) (i : Nat) : List Nat := match i with
  | 0 => []
  | succ n => toByte (c, utf8Size c - succ n) :: (Char_toUTF8_aux c n)

def Char_toUTF8 (c : Char) := Char_toUTF8_aux c (utf8Size c)

/- Convert a string s into it UTF8 encoding-/
def Str_toUTF8 (s: Str) : List Nat := match s with
  | [] => []
  | h::t => (Char_toUTF8_aux h (utf8Size h)) ++  Str_toUTF8 t

lemma Char_toUTF8_aux_ne_nil (g: i > 0) : Char_toUTF8_aux c i ≠ [] := by
  induction i ;contradiction
  rename_i n ind
  unfold Char_toUTF8_aux
  cases n ; simp only [zero_eq, reduceSucc, ne_eq, not_false_eq_true, not_sym]
  simp only [gt_iff_lt, zero_lt_succ, ne_eq, forall_true_left] at ind
  simp only [ne_eq, not_false_eq_true, not_sym]

lemma Char_toUTF8_ne_nil : Char_toUTF8 c  ≠ [] := by
  apply Char_toUTF8_aux_ne_nil; apply utf8Size_pos

lemma Char_toUTF8_aux_length: (Char_toUTF8_aux c i).length = i :=by
  induction i; simp only [Char_toUTF8_aux, length_nil]
  rename_i n ind
  unfold Char_toUTF8_aux; simp only [length_cons, succ.injEq]
  cases n; simp only [Char_toUTF8_aux, length_nil, zero_eq]
  unfold Char_toUTF8_aux; simp only [length_cons, succ.injEq]
  simp only [gt_iff_lt, zero_lt_succ, Char_toUTF8_aux, length_cons, succ.injEq, forall_true_left] at ind
  exact ind

lemma Char_toUTF8_length : (Char_toUTF8 c).length = utf8Size c := Char_toUTF8_aux_length

lemma all_bytes_eq_of_Char_eq_aux (gn: n ≤ utf8Size c1): Char_toUTF8_aux c1 n = Char_toUTF8_aux c2 n
          →  (∀ i < n, toByte (c1, utf8Size c1 - succ i) =  toByte (c2, utf8Size c2 - succ i)) :=by
  induction n generalizing c1 c2
  unfold Char_toUTF8_aux
  simp only [zero_eq, not_lt_zero', IsEmpty.forall_iff, forall_const, forall_true_left]
  rename_i n ind
  intro g x gx
  unfold Char_toUTF8_aux at g
  have g:= List.cons_eq_cons.mp g
  have gn' : n ≤ utf8Size c1 := by linarith
  have ind:= ind gn' g.right;
  by_cases (x < n); rename_i g0
  simp only [g0, ind]
  have g0: x = n := by linarith
  rw[g0]; exact g.left

lemma all_bytes_eq_of_Char_eq: Char_toUTF8 c1 = Char_toUTF8 c2 → (∀ i < utf8Size c1, toByte (c1, i) = toByte (c2, i)) := by
  unfold Char_toUTF8
  have c1p: utf8Size c1 > 0 := by apply utf8Size_pos
  have c2p: utf8Size c2 > 0 := by apply utf8Size_pos
  intro g
  have hcp:= g
  unfold Char_toUTF8_aux at hcp
  split at hcp; linarith; split at hcp; linarith
  rename_i i1 n1 g1 i2 n2 g2
  have hcp:= List.cons_eq_cons.mp hcp
  simp only [g1, ge_iff_le, le_refl, tsub_eq_zero_of_le, g2] at hcp
  have gsize: utf8Size c1 = utf8Size c2:= Char_size_eq_of_firstbyte_eq hcp.left
  rw[← gsize] at g
  have gn: utf8Size c1 ≤ utf8Size c1 := by simp only [le_refl]
  have gaux:= all_bytes_eq_of_Char_eq_aux gn g
  intro x gx
  have : utf8Size c1 - succ x < utf8Size c1 :=by omega
  rw[← gsize] at gaux
  have main: toByte (c1, utf8Size c1 - succ (utf8Size c1 - succ x)) = toByte (c2, utf8Size c1 - succ (utf8Size c1 - succ x))
      := by simp only [gaux,this]
  have e : utf8Size c1 - succ (utf8Size c1 - succ x) = x := by
    have e0: utf8Size c1 - succ (utf8Size c1 - succ x) = utf8Size c1 - (utf8Size c1 - succ x) -1
      := by apply Nat.sub_succ'
    rw[e0]
    have e1: utf8Size c1 - (utf8Size c1 - succ x) =  succ x
      :=by apply Nat.sub_sub_self; linarith
    rw[e1]; simp only [succ_eq_add_one, add_tsub_cancel_right]
  rw[e] at main; exact main


lemma char_eq_of_toByteList_prefix : List.IsPrefix (Char_toUTF8 c1) (Char_toUTF8 c2) →  c1 = c2 := by
  unfold Char_toUTF8
  intro g
  have g2: utf8Size c1 = utf8Size c2 := by
    unfold Char_toUTF8_aux at g
    have i1: utf8Size c1 ≠ 0 := by apply Nat.ne_of_gt; apply utf8Size_pos
    have i2: utf8Size c2 ≠  0 := by apply Nat.ne_of_gt; apply utf8Size_pos
    split at g ; contradiction ; split at g; contradiction
    simp only [succ_eq_add_one, le_refl, tsub_eq_zero_of_le, *] at g;
    exact Char_size_eq_of_firstbyte_eq (prefix_cons g).left
  have l1: (Char_toUTF8_aux c1 (utf8Size c1)).length = utf8Size c1 :=by apply Char_toUTF8_length
  have l2: (Char_toUTF8_aux c2 (utf8Size c2)).length = utf8Size c2 :=by apply Char_toUTF8_length
  have l3: (Char_toUTF8_aux c1 (utf8Size c1)).length = (Char_toUTF8_aux c2 (utf8Size c2)).length := by
    rw[l1, l2] ; exact g2
  have ge : Char_toUTF8_aux c1 (utf8Size c1) = Char_toUTF8_aux c2 (utf8Size c2) := by
    apply prefix_eq_self g l3
  by_contra; rename_i gc
  have ge:= all_bytes_eq_of_Char_eq ge
  have gc: ∃ i , i < utf8Size c1 ∧  toByte (c1,i) ≠ toByte (c2,i) := exists_byte_ne_of_Chat_ne gc
  obtain ⟨i, hb⟩ :=gc
  have : toByte (c1, i) = toByte (c2, i) := by simp only [hb.left, ge]
  simp only [this, ne_eq, not_true_eq_false, and_false] at hb


theorem prefix_iff_listByte_prefix : List.IsPrefix (Str_toUTF8 p) (Str_toUTF8 s) ↔ List.IsPrefix p s := by
  induction p generalizing s
  simp only [Str_toUTF8, _root_.nil_prefix]
  rename_i hp tp ind
  cases s
  simp only [Str_toUTF8, prefix_nil, append_eq_nil, not_false_eq_true, not_sym, iff_false, not_and] ;
  have : Char_toUTF8_aux hp (utf8Size hp) ≠  [] := by apply Char_toUTF8_ne_nil
  simp only [this, not_false_eq_true, not_sym, false_implies]
  rename_i hs ts ; simp [Str_toUTF8] ;
  constructor
  intro gc
  have go:= prefix_append_or gc
  cases go; rename_i go; have go:= char_eq_of_toByteList_prefix go
  rw [go]; apply prefix_cons_mpr
  rw [go] at gc;
  have gc:= (List.prefix_append_right_inj (Char_toUTF8_aux hs (utf8Size hs))).mp gc
  simp only [ind.mp, gc]
  rename_i go; have go:= char_eq_of_toByteList_prefix go
  rw [go]; apply prefix_cons_mpr
  rw [go] at gc;
  have gc:= (List.prefix_append_right_inj (Char_toUTF8_aux hp (utf8Size hp))).mp gc
  simp only [ind.mp, gc]
  intro g ; have g:= prefix_cons g
  rw [g.left];
  apply (prefix_append_right_inj (Char_toUTF8_aux hs (utf8Size hs))).mpr
  simp only [ind.mpr, g.right]
