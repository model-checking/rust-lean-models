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

lemma substring_charpos_map : substring_charpos s ss = some i →
        ∃ j, substring_charpos (List.map f (v ++ s)) (List.map f ss) = some j ∧ j ≤ i + v.length := by
  intro g
  have g:= substring_charpos_some_sound.mp g
  unfold is_first_substringcharpos at g
  have g:= g.left
  have gi : is_substringcharpos (List.map f (v ++ s)) (List.map f ss) (i + v.length)  := by
    unfold is_substringcharpos at * ; obtain ⟨s0, s2, g⟩:= g
    use List.map f (v++s0), List.map f s2;
    simp only [g, List.append_assoc, map_append, length_append, length_map, true_and]; omega
  have gj := exists_first_substring_charpos (by use (i + v.length))
  obtain ⟨j, gj⟩ := gj; use j
  constructor
  . exact substring_charpos_some_sound.mpr gj
  . unfold is_first_substringcharpos at gj
    exact gj.right (i + v.length) gi


lemma sub_split_map (gss: ss.length > 0):
    (split_substring s ss).length ≤  (split_substring (List.map f (v++s)) (List.map f ss)).length :=by
  generalize gl: s.length = l
  induction l using Nat.strong_induction_on generalizing s v
  rename_i n ind
  by_cases (s.length = 0)
  rename_i gs; have gs:= List.eq_nil_of_length_eq_zero gs
  rw[gs]; unfold split_substring; simp only [gt_iff_lt, gss, ↓reduceDIte, take_nil, drop_nil,
    map_nil, length_nil, lt_self_iff_false, singleton_append, length_cons, List.length_singleton,
    reduceSucc, ge_iff_le]
  have i:= @substring_charpos_of_nil ss gss; rw[i]
  simp only [List.length_singleton, length_map, gss, ↓reduceDIte, ge_iff_le]
  split ; simp only [List.append_nil, List.length_singleton, le_refl];
  simp only [List.append_nil,length_cons]; omega
  unfold split_substring; simp only [gt_iff_lt, gss, ↓reduceDIte, length_map, ge_iff_le]
  split; split; simp only [List.length_singleton, le_refl]
  simp only [List.length_singleton, length_cons]; simp only [length_nil, reduceSucc]; omega
  rename_i i gi
  have gj:= @substring_charpos_map _ _ _ f v gi; obtain ⟨j,gj⟩ := gj; rw[gj.left]
  simp only [length_cons, ge_iff_le];
  generalize gm: (List.drop (i + ss.length) s).length = m
  have id1: m < n :=by rw[← gm, ← gl]; simp only [length_drop]; omega
  rw[← List.map_drop]
  have gu: ∃ u, u ++ List.drop (i + ss.length) s = List.drop (j + ss.length) (v ++ s):= by
    by_cases j + ss.length ≤  v.length ; rename_i gx
    rw [List.drop_append_of_le_length gx]
    use (v.drop (j + ss.length)) ++ (s.take (i + ss.length))
    simp only [List.append_assoc, take_append_drop]
    have : j + ss.length = v.length + (j + ss.length - v.length) := by omega
    rw[this, List.drop_append];
    have : i + ss.length = ((i + ss.length) - (j + ss.length - v.length)) + (j + ss.length - v.length) := by omega
    rw[this, ← List.drop_drop]
    use List.take (i + ss.length - (j + ss.length - v.length)) (List.drop (j + ss.length - v.length) s)
    rw[List.take_append_drop]
  obtain⟨u, gu⟩:= gu; rw[← gu]
  exact Nat.succ_le_succ (@ind m id1 _ u gm)

lemma split_map (gss: ss.length > 0):
    (split_substring s ss).length ≤  (split_substring (List.map f s) (List.map f ss)).length :=by
  have := @sub_split_map s ss f [] gss; simp only [nil_append] at this; exact this
