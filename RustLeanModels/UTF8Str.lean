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

def isValid (e : Char ×  Nat) : Bool := e.2 < utf8Size e.1

axiom Char_Pos0 : ∀ c1 c2 b, b ≠ 0 → toByte (c1,0) ≠ toByte (c2,b)

axiom Char_Diff : ∀ c1 c2, c1 ≠ c2 → ∃ b , b < utf8Size c1 ∧  toByte (c1,b) ≠ toByte (c2,b)

axiom Char_Size : ∀ c1 c2,  toByte (c1,0) = toByte (c2,0) →  utf8Size c1 = utf8Size c2

def Char_toUTF8 (c : Char) (i : Nat) : List Nat := match i with
  | 0 => []
  | succ n => toByte (c, utf8Size c - succ n) :: (Char_toUTF8 c n)

def Str_toUTF8 (s: Str) : List Nat := match s with
  | [] => []
  | h::t => (Char_toUTF8 h (utf8Size h)) ++  Str_toUTF8 t


lemma Char_toUTF8_neq_nil_aux (h: i > 0) : Char_toUTF8 c i ≠ [] := by
  induction i ;contradiction
  rename_i n ind
  unfold Char_toUTF8
  cases n ; simp only [zero_eq, reduceSucc, ne_eq, not_false_eq_true, not_sym]
  simp only [gt_iff_lt, zero_lt_succ, ne_eq, forall_true_left] at ind
  simp only [ne_eq, not_false_eq_true, not_sym]

lemma Char_toUTF8_neq_nil : Char_toUTF8 c (utf8Size c) ≠ [] := by
  apply Char_toUTF8_neq_nil_aux; apply utf8Size_pos

lemma Char_toUTF8_length_aux (h: i > 0) : (Char_toUTF8 c i).length = i :=by
  induction i; contradiction
  rename_i n ind
  unfold Char_toUTF8; simp only [length_cons, succ.injEq]
  cases n; simp only [Char_toUTF8, length_nil, zero_eq]
  unfold Char_toUTF8; simp only [length_cons, succ.injEq]
  simp only [gt_iff_lt, zero_lt_succ, Char_toUTF8, length_cons, succ.injEq, forall_true_left] at ind
  exact ind


lemma Char_toUTF8_length : (Char_toUTF8 c (utf8Size c)).length = utf8Size c :=by
  apply Char_toUTF8_length_aux;  apply utf8Size_pos

lemma eq_list_eq_mem_aux (hn: n ≤ utf8Size c1): Char_toUTF8 c1 n = Char_toUTF8 c2 n
          →  (∀ b < n, toByte (c1, utf8Size c1 -succ b) =  toByte (c2, utf8Size c2 - succ b)) :=by
  induction n generalizing c1 c2
  unfold Char_toUTF8
  simp only [zero_eq, not_lt_zero', IsEmpty.forall_iff, forall_const, forall_true_left]
  rename_i n ind
  intro h x hx
  unfold Char_toUTF8 at h
  have h:= List.cons_eq_cons.mp h
  have hn' : n ≤ utf8Size c1 := by linarith
  have ind:= ind hn' h.right;
  by_cases (x < n); rename_i h0
  simp only [h0, ind]
  have h0: x = n := by linarith
  rw[h0]; exact h.left

lemma eq_list_eq_mem: Char_toUTF8 c1 (utf8Size c1) = Char_toUTF8 c2 (utf8Size c2)
      → (∀ b < utf8Size c1, toByte (c1, b) =  toByte (c2, b)) := by
  have c1p: utf8Size c1 > 0 := by apply utf8Size_pos
  have c2p: utf8Size c2 > 0 := by apply utf8Size_pos
  intro h
  have hcp:= h
  unfold Char_toUTF8 at hcp
  split at hcp; linarith; split at hcp; linarith
  rename_i i1 n1 h1 i2 n2 h2
  have hcp:= List.cons_eq_cons.mp hcp
  simp only [h1, ge_iff_le, le_refl, tsub_eq_zero_of_le, h2] at hcp
  have hsize: utf8Size c1 = utf8Size c2:= by apply Char_Size c1 c2  hcp.left
  rw[← hsize] at h
  have hn: utf8Size c1 ≤ utf8Size c1 := by simp
  have haux:= eq_list_eq_mem_aux hn h
  intro x hx
  have : utf8Size c1 - succ x < utf8Size c1 :=by apply Nat.sub_lt_self; simp; linarith
  rw[← hsize] at haux
  have main: toByte (c1, utf8Size c1 - succ (utf8Size c1 - succ x)) = toByte (c2, utf8Size c1 - succ (utf8Size c1 - succ x))
      := by simp only [haux,this]
  have e : utf8Size c1 - succ (utf8Size c1 - succ x) = x := by
    have e0: utf8Size c1 - succ (utf8Size c1 - succ x) = utf8Size c1 - (utf8Size c1 - succ x) -1
      := by apply Nat.sub_succ'
    rw[e0]
    have e1: utf8Size c1 - (utf8Size c1 - succ x) =  succ x
      :=by apply Nat.sub_sub_self; linarith
    rw[e1]; simp
  rw[e] at main; exact main


lemma char_eq_of_toByteList_prefix : List.IsPrefix (Char_toUTF8 c1 (utf8Size c1)) (Char_toUTF8 c2 (utf8Size c2)) →  c1 = c2 := by
  intro h
  have h2: utf8Size c1 = utf8Size c2 := by
    unfold Char_toUTF8 at h
    have i1: utf8Size c1 ≠ 0 := by apply Nat.ne_of_gt; apply utf8Size_pos
    have i2: utf8Size c2 ≠  0 := by apply Nat.ne_of_gt; apply utf8Size_pos
    split at h ; contradiction ; split at h; contradiction
    simp [*] at h;
    exact Char_Size c1 c2 (prefix_cons h).left
  have l1: (Char_toUTF8 c1 (utf8Size c1)).length = utf8Size c1 :=by apply Char_toUTF8_length
  have l2: (Char_toUTF8 c2 (utf8Size c2)).length = utf8Size c2 :=by apply Char_toUTF8_length
  have l3: (Char_toUTF8 c1 (utf8Size c1)).length = (Char_toUTF8 c2 (utf8Size c2)).length := by
    rw[l1, l2] ; exact h2
  have he : Char_toUTF8 c1 (utf8Size c1) = Char_toUTF8 c2 (utf8Size c2) := by
    apply prefix_eq_self h l3
  by_contra; rename_i hc
  have he:= eq_list_eq_mem he
  have hc: ∃ b , b < utf8Size c1 ∧  toByte (c1,b) ≠ toByte (c2,b) := by apply Char_Diff; simp; exact hc
  obtain ⟨b, hb⟩ :=hc
  have : toByte (c1, b) = toByte (c2, b) := by simp[he, hb.left]
  simp [this] at hb


theorem listByte_prefix : List.IsPrefix (Str_toUTF8 p) (Str_toUTF8 s) ↔ List.IsPrefix p s := by
  induction p generalizing s
  simp [Str_toUTF8, List.nil_prefix]
  rename_i hp tp ind
  cases s
  simp [Str_toUTF8] ;
  have : Char_toUTF8 hp (utf8Size hp) ≠  [] := by apply Char_toUTF8_neq_nil
  simp [this]
  rename_i hs ts ; simp [Str_toUTF8] ;
  constructor
  intro hc
  have ho:= prefix_append_or hc
  cases ho; rename_i ho; have ho:= char_eq_of_toByteList_prefix ho
  rw [ho]; apply prefix_cons_mpr
  rw [ho] at hc;
  have hc:= (List.prefix_append_right_inj (Char_toUTF8 hs (utf8Size hs))).mp hc
  simp only [ind.mp, hc]
  rename_i ho; have ho:= char_eq_of_toByteList_prefix ho
  rw [ho]; apply prefix_cons_mpr
  rw [ho] at hc;
  have hc:= (List.prefix_append_right_inj (Char_toUTF8 hp (utf8Size hp))).mp hc
  simp only [ind.mp, hc]
  intro h ; have h:= prefix_cons h
  rw [h.left];
  apply (prefix_append_right_inj (Char_toUTF8 hs (utf8Size hs))).mpr
  simp only [ind.mpr, h.right]
