-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
import RustLeanModels.Basic
import RustLeanModels.RustString
import Lean
open RustString
open List
open Mathlib
open Nat
set_option maxHeartbeats 10000000


/-Sometimes adding an extra variable makes to proof easier-/

lemma substring_charpos_map : substring_charpos s s1 = some p →
        ∃ q, substring_charpos (List.map f (v ++ s)) (List.map f s1) = some q ∧ q ≤ p + v.length := by
  intro g
  have g:= substring_charpos_some_sound.mp g
  unfold is_first_substringcharpos at g
  have g:= g.left
  have gp : is_substringcharpos (List.map f (v ++ s)) (List.map f s1) (p + v.length)  := by
    unfold is_substringcharpos at * ; obtain ⟨s0, s2, g⟩:= g
    use List.map f (v++s0), List.map f s2;
    simp only [g, List.append_assoc, map_append, length_append, length_map, true_and]; omega
  have gq := exists_first_substring_charpos (by use (p + v.length))
  obtain ⟨q, gq⟩ := gq; use q
  constructor
  . exact substring_charpos_some_sound.mpr gq
  . unfold is_first_substringcharpos at gq
    exact gq.right (p + v.length) gp


lemma sub_split_map (gs1: s1.length > 0):
    (split_substring s s1).length ≤  (split_substring (List.map f (v++s)) (List.map f s1)).length :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s v
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs
  rw[gs]; unfold split_substring; simp only [gt_iff_lt, gs1, ↓reduceDIte, take_nil, drop_nil,
    map_nil, length_nil, lt_self_iff_false, singleton_append, length_cons, List.length_singleton,
    reduceSucc, ge_iff_le]
  have i:= @substring_charpos_of_nil s1 gs1; rw[i]
  simp only [List.length_singleton, length_map, gs1, ↓reduceDIte, ge_iff_le]
  split ; simp only [List.append_nil, List.length_singleton, le_refl];
  simp only [List.append_nil,length_cons]; omega
  unfold split_substring; simp only [gt_iff_lt, gs1, ↓reduceDIte, length_map, ge_iff_le]
  split; split; simp only [List.length_singleton, le_refl]
  simp only [List.length_singleton, length_cons]; simp only [length_nil, reduceSucc]; omega
  rename_i p gp
  have gq:= @substring_charpos_map _ _ _ f v gp; obtain ⟨q,gq⟩ := gq; rw[gq.left]
  simp only [length_cons, ge_iff_le];
  generalize gm: (List.drop (p + s1.length) s).length = m
  have id1: m < n :=by rw[← gm, ← gl]; simp only [length_drop]; omega
  rw[← List.map_drop]
  have gu: ∃ u, u ++ List.drop (p + s1.length) s = List.drop (q + s1.length) (v ++ s):= by
    by_cases q + s1.length ≤  v.length ; rename_i gx
    rw [List.drop_append_of_le_length gx]
    use (v.drop (q + s1.length)) ++ (s.take (p + s1.length))
    simp only [List.append_assoc, take_append_drop]
    have : q + s1.length = v.length + (q + s1.length - v.length) := by omega
    rw[this, List.drop_append];
    have : p + s1.length = ((p + s1.length) - (q + s1.length - v.length)) + (q + s1.length - v.length) := by omega
    rw[this, ← List.drop_drop]
    use List.take (p + s1.length - (q + s1.length - v.length)) (List.drop (q + s1.length - v.length) s)
    rw[List.take_append_drop]
  obtain⟨u, gu⟩:= gu; rw[← gu]
  exact Nat.succ_le_succ (@ind m id1 _ u gm)

lemma split_map (gs1: s1.length > 0):
    (split_substring s s1).length ≤  (split_substring (List.map f s) (List.map f s1)).length :=by
  have := @sub_split_map s s1 f [] gs1; simp only [nil_append] at this; exact this
