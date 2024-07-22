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


/- Let's start with a simple example-/
/- This function is supposed to return the length of the longest commpn prefix of 2 strings s1 s2 -/
def LCP_length (s1 s2: Str) := match s1, s2 with
  | [] , _ => 0
  | _, [] => 0
  | h1::t1, h2::t2 => if h1 ≠ h2 then 0 else 1 + LCP_length t1 t2

/- We want to verify the correctness of this function-/
/- Firstly, we need to formalize the correctness property as : -/
def is_LCP_length (s1 s2: Str) (l: Nat) := (∃ pre, List.IsPrefix pre s1 ∧ List.IsPrefix pre s2 ∧ pre.length = l) ∧
                            (∀ p, List.IsPrefix p s1 ∧ List.IsPrefix p s2 → p.length ≤ l)

/- From the definition above, we formalize the correctness theorem of the LCP_length as:

    theorem LCP_length_correct : LCP_length s1 s2 = l ↔ is_LCP_length s1 s2 l
-/

/- Firstly, we prove the modus ponen (mp) direction of the theorem by induction-/
lemma LCP_length_correct_mp : LCP_length s1 s2 = l → is_LCP_length s1 s2 l:= by
  induction s1 generalizing s2 l
  simp only [LCP_length]; intro g; rw[← g]
  simp only [is_LCP_length, prefix_nil, length_eq_zero, and_imp, forall_eq, _root_.nil_prefix,
    length_nil, _root_.zero_le, imp_self, and_true, exists_eq_left, and_self]
  rename_i h1 t1 ind
  cases s2
  . simp only [LCP_length]; intro g; rw[← g]
    simp only [is_LCP_length, prefix_nil, length_eq_zero, and_imp, and_self_left]
    constructor
    . use []; simp only [_root_.nil_prefix, and_self]
    . intro p _ g2; simp only [g2, length_nil, le_refl]
  . rename_i h2 t2; simp only [LCP_length, ne_eq, ite_not, is_LCP_length, and_imp]
    split
    . intro g; rename_i gh;
      have ind:= @ind t2 (l-1) (by omega); unfold is_LCP_length at ind; obtain ⟨pre, gp⟩:= ind.left
      constructor
      . use (h2::pre); rw[gh]; simp only [prefix_cons_inj, gp, length_cons, true_and]; omega
      . intro p0 g1p0 g2p0; cases p0; simp only [length_nil, _root_.zero_le]
        rename_i hp0 tp0;
        have g1p0:= prefix_cons g1p0; have g2p0:= prefix_cons g2p0;
        have ind:= ind.right tp0 ⟨g1p0.right, g2p0.right⟩
        simp only [length_cons, ge_iff_le]; omega
    . intro g; rw[← g];
      constructor
      . use []
        simp only [_root_.nil_prefix, length_nil, nonpos_iff_eq_zero, length_eq_zero,true_and]
      . intro p gp1 gp2; cases p; simp only [length_nil, le_refl]
        rename_i gh hp tp;
        have gp1:= prefix_cons gp1; have gp2:= prefix_cons gp2;
        simp only [← gp1.left, ← gp2.left, not_true_eq_false] at gh

/- For the modus ponen reverse (mpr) direction, we can prove it by induction,
  but it is more convenient if we use the "mpr_of_unique" theorem (Basic.lean) instead
  (see the definition of "unique" and "mpr_of_unique" in Basic.lean for more details)
-/

/- First, we need to prove that the function "is_LCP_length s1 s2 : Nat → Prop" is "unique"
    (there is a only one value l such that "is_LCP_length s1 s2 l")
 -/
lemma is_LCP_length_unique:  unique (is_LCP_length s1 s2) := by
  unfold unique; intro l1 l2 g1 g2
  unfold is_LCP_length at g1 g2
  have ⟨p1, g1l⟩ := g1.left; have ⟨p2, g2l⟩ := g2.left
  have g1r:= g1.right p2 ⟨g2l.left, g2l.right.left⟩
  have g2r:= g2.right p1 ⟨g1l.left, g1l.right.left⟩
  omega

/- The correctness theorem-/
theorem LCP_length_correct : LCP_length s1 s2 = l ↔ is_LCP_length s1 s2 l := by
  apply mpr_of_unique (by intro l ; exact LCP_length_correct_mp) is_LCP_length_unique

/-Sometimes the function is defined recursively with extra parameters.
  In this case, there is an _aux function with the extra parameters
                      and a main functions which assign initial values for those parameters
  For example:    -/

def LCP_length_aux (s1 s2: Str) (k: Nat) := match s1, s2 with
  | [] , _ => k
  | _, [] => k
  | h1::t1, h2::t2 => if h1 ≠ h2 then k else LCP_length_aux t1 t2 (k+1)

def LCP_length_version2 (s1 s2: Str) := LCP_length_aux s1 s2 0

/-
  This function is should be equivalent to LCP_length function.
  Supposed that we want to prove the equivalence of them.
  There are 2 ways to construct an induction proof for recursive functions with extra parameters (each with pros and cons):
    1. Firstly, construct prove on the "_aux" function (as a general version). Then derive the proof for the main function.
      Pros: no extra lemmas.
      Cons: hard to write the theorem statement.

    2. Directly on the main function. (Prefered)
      Pros: Write the theorem statement is straightforward.
      Cons: Requires lemmas for manipulating the extra parameters of the "_aux" theorem.
      However, those lemmas (name: "func_name_aux_para1_[some operation]") are very useful.
-/


--Here is the demonstration of the first way

lemma LCP_length_aux_EQ : LCP_length_aux s1 s2 k = k + LCP_length s1 s2 :=by
  induction s1 generalizing k s2
  simp only [LCP_length_aux, LCP_length, add_zero]
  rename_i h1 t1 ind
  cases s2
  . simp only [LCP_length_aux, LCP_length, add_zero]
  . simp only [LCP_length_aux, ne_eq, ite_not, LCP_length]
    split
    . rw[ind, add_assoc]
    . simp only [add_zero]

theorem LCP_length_EQ_first_way : LCP_length_version2 s1 s2  = LCP_length s1 s2 :=by
  unfold LCP_length_version2;
  simp only [LCP_length_aux_EQ, zero_add]

--Here is the demonstration of the second way

lemma LCP_length_aux_para1_elim: LCP_length_aux s1 s2 k = k + LCP_length_aux s1 s2 0 :=by
  induction s1 generalizing k s2
  simp only [LCP_length_aux, add_zero]
  rename_i h1 t1 ind
  cases s2
  . simp only [LCP_length_aux, add_zero]
  . simp only [LCP_length_aux, ne_eq, ite_not, zero_add]
    split
    . rw[ind, @ind _ 1, add_assoc]
    . simp only [add_zero]

theorem LCP_length_EQ_second_way : LCP_length_version2 s1 s2  = LCP_length s1 s2 :=by
  induction s1 generalizing s2
  simp only [LCP_length_version2, LCP_length_aux, LCP_length]
  rename_i h1 t1 ind
  cases s2
  . simp only [LCP_length_version2, LCP_length_aux, LCP_length]
  . simp only [LCP_length_version2, LCP_length_aux, ne_eq, zero_add, ite_not, LCP_length]
    split
    . -- use the parameter manipulating lemma here
      rw[LCP_length_aux_para1_elim, ← LCP_length_version2, ind]
    . simp only


/-
  Let's move on to a more complicated function
  This example demonstrates a difficult case where both of the two ways above stuck, because
  1. For the first way: It is very hard to state an "_aux" lemma (like "LCP_length_aux_EQ")
  2. For the second way: We need a parameter manipulating lemma (like "LCP_length_aux_para1_elim")
      to prove the main theorem, but to prove the lemma, we need the main theorem
  To overcome the difficulty in the second way, we can use this trick:
    "When we need an induction assumption of A to prove B and vice versa, prove (A ∧ B) instead" "
-/

/-The function "LCS_length" should calculate the length of the longest common substring of the two strings s1 s2-/
def LCS_length_aux (s1 s2: Str) (k: Nat) := match s1, s2 with
  | [] , _ => k
  | _, [] => k
  | h1::t1, h2::t2 => if h1 ≠ h2 then Nat.max (Nat.max (LCS_length_aux (h1::t1) t2 0) (LCS_length_aux t1 (h2::t2) 0)) k
                      else Nat.max (Nat.max (LCS_length_aux (h1::t1) t2 0) (LCS_length_aux t1 (h2::t2) 0)) (LCS_length_aux t1 t2 (k+1))
termination_by s1.length + s2.length

def LCS_length (s1 s2: Str) := LCS_length_aux s1 s2 0

def is_LCS_length (s1 s2) (k:Nat):= (∀ s, (contains_substring s1 s ∧ contains_substring s2 s) → s.length ≤ k )
                            ∧ (∃ s, (contains_substring s1 s ∧ contains_substring s2 s ∧ s.length = k))

/- Here are some supporting lemmas, the main lemma "LCS_length_correct_mp" at line 355-/


/- Some supporting lemmas-/

lemma common_substring_cons: contains_substring (h1 :: t1) s = true ∧ contains_substring (h2 :: t2) s = true
    →  (contains_substring t1 s) ∨ (contains_substring t2 s) ∨ (List.isPrefixOf s (h1 :: t1) ∧ List.isPrefixOf s (h2 :: t2)):=by
  intro g; cases s
  . simp only [contains_substring, isPrefixOf, and_self, or_self]
  . simp only [contains_substring, Bool.if_true_left, Bool.decide_eq_true, Bool.or_eq_true] at g
    cases g.left
    . cases g.right
      . rename_i g1 g2; simp only [g1, g2, and_self, or_true]
      . rename_i gc; simp only [gc, true_or, or_true]
    . rename_i gc; simp only [gc, true_or]

lemma common_substring_cons_diff_head: h1 ≠ h2 → contains_substring (h1 :: t1) s = true ∧ contains_substring (h2 :: t2) s = true
    →  (contains_substring t1 s) ∨ (contains_substring t2 s) :=by
  intro gh g; have g:= common_substring_cons g
  by_contra; rename_i gc; simp only [not_or, Bool.not_eq_true] at gc;
  simp only [gc, Bool.false_eq_true, not_false_eq_true, not_sym, false_or] at g
  cases s
  . simp only [contains_substring, Bool.true_eq_false, not_false_eq_true, not_sym, and_self] at gc
  . simp only [isPrefixOf, Bool.and_eq_true, beq_iff_eq] at g;
    simp only [← g.left.left, ← g.right.left, ne_eq, not_true_eq_false] at gh

lemma is_LCS_length_nil_left : is_LCS_length [] s2 0 :=by
  unfold is_LCS_length ;
  simp only [nonpos_iff_eq_zero, length_eq_zero, and_imp, exists_eq_right_right, contains_substring, and_self, and_true]
  intro s; cases s; simp only [implies_true]
  simp only [contains_substring, Bool.false_eq_true, not_false_eq_true, not_sym, imp_false, Bool.not_eq_true, false_implies]

lemma is_LCS_length_nil_right : is_LCS_length s1 [] 0 :=by
  unfold is_LCS_length ;
  simp only [nonpos_iff_eq_zero, length_eq_zero, and_imp, exists_eq_right_right, contains_substring, and_self, and_true]
  intro s; cases s; simp only [implies_true]
  simp only [contains_substring, Bool.false_eq_true, not_false_eq_true, not_sym, imp_self, implies_true]

lemma is_LCS_le_of_contains : is_LCS_length s1 s2 l → (contains_substring s1 s ∧  contains_substring s2 s) → s.length ≤ l := by
  intro g; exact g.left s

lemma is_LCS_length_unique : unique (is_LCS_length s1 s2)  :=by
  unfold unique; intro l1 l2 g1 g2;
  obtain ⟨u1, gt1⟩:= g1.right; obtain ⟨u2, gt2⟩:= g2.right
  have g1:= g1.left u2 ⟨gt2.left, gt2.right.left⟩
  have g2:= g2.left u1 ⟨gt1.left, gt1.right.left⟩
  omega

lemma LCP_length_le_LCS_length: is_LCS_length s1 s2 k → LCP_length s1 s2 ≤ k := by
  intro g
  generalize gl: LCP_length s1 s2 = l
  obtain ⟨pre, gl⟩ := (LCP_length_correct_mp gl).left
  simp only [← IsPrefix_isPrefixOf_EQ] at gl
  have g:=g.left pre ⟨contains_substring_of_isPrefixOf gl.left, contains_substring_of_isPrefixOf gl.right.left⟩
  omega

lemma LCP_length_ne_LCS_length: (¬∃ pre, pre <+: s1 ∧ pre <+: s2 ∧ is_LCS_length s1 s2 pre.length)
                → is_LCS_length s1 s2 ls → ¬ LCP_length s1 s2 = ls := by
  intro g g1
  by_contra; rename_i gc
  have gc:= LCP_length_correct.mp gc; obtain ⟨pre, gc⟩:= gc.left
  have: ∃ pre, pre <+: s1 ∧ pre <+: s2 ∧ is_LCS_length s1 s2 pre.length := by
    use pre; simp only [gc, true_and]; rename_i gl; exact g1
  contradiction

lemma lcp_is_LCS_length: (∃ pre, pre <+: s1 ∧ pre <+: s2 ∧ is_LCS_length s1 s2 pre.length)
                → is_LCS_length s1 s2 ls → LCP_length s1 s2 = ls := by
  intro g g1; obtain ⟨pre, g⟩:=g
  generalize gl: LCP_length s1 s2 = l
  have gl1:= (LCP_length_correct_mp gl).right pre ⟨g.left, g.right.left⟩
  have gl2:= LCP_length_le_LCS_length g.right.right
  have gl3:= is_LCS_length_unique pre.length ls g.right.right g1
  omega


lemma is_LCS_length_add_head_left : (is_LCS_length t1 s2 lct) →  (is_LCS_length (h1::t1) s2 lc) → (lc = lct) ∨ (lc = 1 + lct) :=by
  unfold is_LCS_length; intro g1 g2
  obtain ⟨s, gt2⟩:= g2.right; obtain ⟨s1, gt1⟩:= g1.right
  have e:= g2.left s1 ⟨contains_substring_cons gt1.left, gt1.right.left⟩
  cases s
  . simp only [length_nil] at gt2
    apply Or.intro_left; omega
  . rename_i hs ts; simp only [length_cons] at gt2
    have i1:= g1.left ts ⟨contains_substring_cons_cons gt2.left, contains_substring_substring_cons gt2.right.left⟩
    omega

lemma is_LCS_length_add_head_right : (is_LCS_length s1 t2 lct) →  (is_LCS_length s1 (h2::t2) lc) → (lc = lct) ∨ (lc = 1 + lct) :=by
  unfold is_LCS_length; intro g1 g2
  obtain ⟨s, gt2⟩:= g2.right; obtain ⟨s1, gt1⟩:= g1.right
  have e:= g2.left s1 ⟨gt1.left, contains_substring_cons gt1.right.left⟩
  cases s
  . simp only [length_nil] at gt2
    apply Or.intro_left; omega
  . rename_i hs ts; simp only [length_cons] at gt2
    have i1:= g1.left ts ⟨contains_substring_substring_cons gt2.left, contains_substring_cons_cons gt2.right.left⟩
    omega

lemma is_LCS_length_add_head_left_right : (is_LCS_length t1 t2 lct) →  (is_LCS_length (h1::t1) (h2::t2) lc) → (lc = lct) ∨ (lc = 1 + lct) :=by
  unfold is_LCS_length; intro g1 g2
  obtain ⟨s, gt2⟩:= g2.right; obtain ⟨s1, gt1⟩:= g1.right
  have e:= g2.left s1 ⟨contains_substring_cons gt1.left, contains_substring_cons gt1.right.left⟩
  cases s
  . simp only [length_nil] at gt2
    apply Or.intro_left; omega
  . rename_i hs ts; simp only [length_cons] at gt2
    have i1:= g1.left ts ⟨contains_substring_cons_cons gt2.left, contains_substring_cons_cons gt2.right.left⟩
    omega


lemma LCP_length_aux_para1_add1_le: LCS_length_aux s1 s2 (k + 1) ≤ 1 + LCS_length_aux s1 s2 k := by
  generalize gl: s1.length + s2.length = l
  induction l using Nat.strong_induction_on generalizing s1 s2 k
  rename_i l ind
  unfold LCS_length_aux
  split; omega; omega;
  rename_i h1 t1 h2 t2
  split; exact max_add_right;
  generalize gm: t1.length + t2.length=m
  have id1: m < l := by rw[← gm, ← gl]; simp only [length_cons]; omega
  have ind:= @ind m id1 t1 t2 (k+1) gm
  have i1: ((LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0)).max (LCS_length_aux t1 t2 (k + 1 + 1)) ≤
        ((LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0)).max (1 + LCS_length_aux t1 t2 (k + 1)) := max_le_of_right_le ind
  have i2:((LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0)).max (LCS_length_aux t1 t2 (k + 1) + 1) ≤
        1 + ((LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0)).max (LCS_length_aux t1 t2 (k + 1)) := max_add_right
  have e: LCS_length_aux t1 t2 (k + 1) + 1 = 1 + LCS_length_aux t1 t2 (k + 1) := by omega
  rw[e] at i2 ; omega


lemma sup_LCS_correct1 : h1 = h2 → (¬∃ pre, pre <+: h1 :: t1 ∧ pre <+: h2 :: t2 ∧ is_LCS_length (h1 :: t1) (h2 :: t2) pre.length)
       →  ¬∃ pre, pre <+: t1 ∧ pre <+: t2 ∧ is_LCS_length t1 t2 pre.length := by
  intro gh gc
  by_contra ; rename_i gp; obtain ⟨pre, gp⟩ :=gp
  have: ∃ pre, pre <+: h1 :: t1 ∧ pre <+: h2 :: t2 ∧ is_LCS_length (h1 :: t1) (h2 :: t2) pre.length:= by
    use (h2::pre); rw[gh]; simp only [prefix_cons_inj, gp, length_cons, true_and]
    unfold is_LCS_length ; have gp:=gp.right.right; unfold is_LCS_length at gp
    constructor;
    intro s gs;
    cases s; simp only [length_nil, le_add_iff_nonneg_left, _root_.zero_le]
    rename_i hs ts; simp only [length_cons, add_le_add_iff_right]
    simp only [contains_substring, isPrefixOf, Bool.and_eq_true, beq_iff_eq, Bool.if_true_left,
        Bool.decide_and, Bool.decide_eq_true, Bool.or_eq_true, decide_eq_true_eq] at gs
    cases gs
    rename_i gs1 gs2
    cases gs1
    cases gs2
    . rename_i gs1 gs2; exact gp.left ts ⟨contains_substring_of_isPrefixOf gs1.right, contains_substring_of_isPrefixOf gs2.right⟩
    . rename_i gs1 gs2; exact gp.left ts ⟨contains_substring_of_isPrefixOf gs1.right, contains_substring_substring_cons gs2⟩
    . cases gs2
      rename_i gs1 gs2; exact gp.left ts ⟨contains_substring_substring_cons gs1, contains_substring_of_isPrefixOf gs2.right⟩
      rename_i gs1 gs2; exact gp.left ts ⟨contains_substring_substring_cons gs1, contains_substring_substring_cons gs2⟩
    use (h2::pre);
    simp only [contains_substring, isPrefixOf_cons₂_self, Bool.if_true_left,
      Bool.decide_eq_true, Bool.or_eq_true, length_cons, and_true]
    rename_i gp0; rw[IsPrefix_isPrefixOf_EQ, IsPrefix_isPrefixOf_EQ]; simp only [gp0, true_or, and_self]
  contradiction


lemma sup_LCS_correct2 (g1: ∃ pre, pre <+: h1 :: t1 ∧ pre <+: h2 :: t2 ∧ is_LCS_length (h1 :: t1) (h2 :: t2) pre.length)
       (g2: ¬∃ pre, pre <+: t1 ∧ pre <+: t2 ∧ is_LCS_length t1 t2 pre.length)
       (g3: is_LCS_length (h1 :: t1) (h2 :: t2) lc) (g4: is_LCS_length t1 t2 lct ) : (lc = lct) ∧ (1 + LCP_length t1 t2 = lct):= by
  have g0:= lcp_is_LCS_length g1 g3;
  obtain⟨pre, g1⟩:=g1
  have g1r:= is_LCS_length_unique pre.length lc g1.right.right g3
  simp only [not_exists, not_and] at g2
  have e:= is_LCS_length_add_head_left_right g4 g3
  cases pre
  . simp only [_root_.nil_prefix, length_nil, true_and] at g1r
    have g1: 0 = lct :=by omega
    have g2:= g2 [];
    simp only [_root_.nil_prefix, length_nil, g1, g4, not_true_eq_false, imp_false] at g2
  . rename_i hp tp
    have gt1:= prefix_cons g1.left; have gt2:= prefix_cons g1.right.left;
    simp only [LCP_length, ← gt1.left, ← gt2.left, ne_eq, not_true_eq_false, ↓reduceIte] at g0
    simp only [g0, and_self]
    cases e; assumption; rename_i e
    simp only [length_cons] at g1r
    have e1: lct = tp.length := by omega
    have g2:= g2 tp gt1.right gt2.right
    rw[e1] at g4; contradiction

/-
Only the first Prop of the right-hand-side is the one we want to prove.
However, to prove that we need to prove the other Props, which servers
as the parameter manipulating lemmas.
The design of the right-hand-side requires some back and forth.
-/
lemma LCS_length_correct_mp: (LCS_length s1 s2  = lc) →  (is_LCS_length s1 s2 lc ∧
      ((∃ pre,List.IsPrefix pre s1  ∧ List.IsPrefix pre s2 ∧ is_LCS_length s1 s2 pre.length ) → LCS_length_aux s1 s2 k = k + lc) ∧
      ((¬ ∃ pre, List.IsPrefix pre s1  ∧ List.IsPrefix pre s2 ∧ is_LCS_length s1 s2 pre.length)
       → ((k + LCP_length s1 s2 ≤ lc →  LCS_length_aux s1 s2 k = LCS_length_aux s1 s2 0) ∧
          (k + LCP_length s1 s2 > lc →  LCS_length_aux s1 s2 k = k + LCP_length s1 s2  )  ) )):=by
  --cleaning trivial cases
  generalize gl: s1.length + s2.length = l
  induction l using Nat.strong_induction_on generalizing s1 s2 k lc
  rename_i l ind
  intro g; have gsv:= g; unfold LCS_length LCS_length_aux at g
  split at g
  . rw[← g]; simp only [is_LCS_length_nil_left, prefix_nil, exists_eq_left, _root_.nil_prefix,
    length_nil, and_self, LCS_length_aux, add_zero, imp_self, not_true_eq_false, nonpos_iff_eq_zero,
    add_eq_zero, and_imp, gt_iff_lt, add_pos_iff, self_eq_add_right, false_implies]
  . rw[← g]; simp only [is_LCS_length_nil_right, prefix_nil, LCS_length_aux, add_zero, implies_true, not_exists,
    not_and, LCP_length, nonpos_iff_eq_zero, imp_self, gt_iff_lt, and_self]
  --main case: s1, s2 ≠ nil
  -- get all inductions and inequalities
  rename_i h1 t1 h2 t2
  generalize gm: (h1::t1).length + t2.length = m
  have id1: m < l := by rw[← gm, ← gl]; simp only [length_cons]; omega
  generalize gh1: LCS_length_aux (h1::t1) t2 0 = lch1
  have indh1:= (@ind m id1 (h1::t1) t2 lch1 1 gm gh1).left
  generalize gm: t1.length + (h2::t2).length = m
  have id1: m < l := by rw[← gm, ← gl]; simp only [length_cons]; omega
  generalize gh2: LCS_length_aux t1 (h2::t2) 0 = lch2
  have indh2:= (@ind m id1 t1 (h2::t2) lch2 1 gm gh2).left
  generalize gm: t1.length + t2.length = m
  have id1: m < l := by rw[← gm, ← gl]; simp only [length_cons]; omega
  generalize gt: LCS_length_aux t1 t2 0 = lct
  have indtp1:= @ind m id1 t1 t2 lct (k+1) gm gt
  have indtp:= @ind m id1 t1 t2 lct k gm gt
  have indt1:= @ind m id1 t1 t2 lct 1 gm gt
  have ilch1:= is_LCS_length_add_head_left indt1.left indh1
  have ilch2:= is_LCS_length_add_head_right indt1.left indh2
  have i00: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≤ 1 + lct:= by rw [Nat.max_le]; omega
  have i01: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≥  LCS_length_aux t1 (h2 :: t2) 0 := by
      simp only [ge_iff_le,le_max_iff, le_refl, or_true]
  have i01: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≥  LCS_length_aux (h1 :: t1) t2 0 := by
      simp only [ge_iff_le, le_max_iff, le_refl, true_or]
  have i1: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≥  lct:= by omega
  have i2: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≤ lc:= by
    split at g;
    . rw[← g]; simp only [le_max_iff, _root_.zero_le, or_self, max_eq_left, le_refl]
    . rw[← g]; simp only [zero_add, le_max_iff, le_refl, max_le_iff, true_or]
  have e0: (lc = lct) ∨ (lc = lct + 1):= by
    split at g
    . simp only [le_max_iff, _root_.zero_le, or_self, max_eq_left] at g; omega
    . have := @LCP_length_aux_para1_add1_le t1 t2 0
      have u: lc ≤ 1 + lct :=by rw[←g, Nat.max_le]; omega
      omega
  have ih1: lch1 ≤ lc := by omega
  have ih2: lch2 ≤ lc := by omega
  --prove is_LCS_length (h1 :: t1) (h2 :: t2) lc
  have glc: is_LCS_length (h1 :: t1) (h2 :: t2) lc := by
    split at g
    . unfold is_LCS_length; constructor
      . intro s gs; rename_i gh
        have gc:= common_substring_cons_diff_head gh gs
        cases gc
        . rename_i gc; have:= is_LCS_le_of_contains indh2 ⟨gc, gs.right⟩ ; omega
        . rename_i gc; have:= is_LCS_le_of_contains indh1 ⟨gs.left, gc⟩; omega
      . simp only [le_max_iff, _root_.zero_le, or_self, max_eq_left] at g; symm at g;
        have g:= cases_max g; cases g
        . obtain⟨s, indh1⟩ := indh1.right
          rename_i g; rw[g, gh1]; use s
          simp only [indh1, contains_substring_cons, and_self]
        . obtain⟨s, indh2⟩ := indh2.right
          rename_i g; rw[g, gh2]; use s
          simp only [indh2, contains_substring_cons, and_self]
    . unfold is_LCS_length; constructor
      . intro s gs; rename_i gh; simp only [ne_eq, Decidable.not_not] at gh;
        cases s; simp only [length_nil, _root_.zero_le]; rename_i hs ts
        have gs:= common_substring_cons gs
        cases gs
        . rename_i gc; have:= is_LCS_le_of_contains indh2 ⟨gc, gs.right⟩ ; omega
        . rename_i gs; cases gs
          . rename_i gc; have:= is_LCS_le_of_contains indh1 ⟨gs.left, gc⟩ ; omega
          . rename_i gs; simp only [isPrefixOf, Bool.and_eq_true, beq_iff_eq] at gs
            have i0:= is_LCS_le_of_contains indtp.left ⟨contains_substring_of_isPrefixOf gs.left.right, contains_substring_of_isPrefixOf gs.right.right⟩
            simp only [length_cons, ge_iff_le]
            by_contra
            have e: ts.length = lct :=by omega
            have : ∃ pre, pre <+: t1 ∧ pre <+: t2 ∧ is_LCS_length t1 t2 pre.length:= by
              use ts; rw[← IsPrefix_isPrefixOf_EQ, ← IsPrefix_isPrefixOf_EQ, e];
              simp only [gs, indtp, and_self]
            have indt1:= indt1.right.left this
            have : lc ≥ LCS_length_aux t1 t2 1 :=by
              simp only [← g, zero_add, ge_iff_le, le_max_iff, le_refl, or_true]
            omega
      . simp only [zero_add] at g; symm at g;
        have g:= cases_max g
        cases g
        . rename_i g; have g:= cases_max g
          cases g
          . obtain⟨s, indh1⟩ := indh1.right
            rename_i g; rw[g, gh1]; use s
            simp only [indh1, contains_substring_cons, and_self]
          . obtain⟨s, indh2⟩ := indh2.right
            rename_i g; rw[g, gh2]; use s
            simp only [indh2, contains_substring_cons, and_self]
        . by_cases (¬ ∃ pre, List.IsPrefix pre t1  ∧ List.IsPrefix pre t2 ∧ is_LCS_length t1 t2 pre.length)
          . rename_i gc
            have i1: LCP_length t1 t2 ≤ lct := LCP_length_le_LCS_length indt1.left
            have i2 := LCP_length_ne_LCS_length gc indt1.left
            have : 1 + LCP_length t1 t2 ≤ lct := by omega
            have ind3:= indt1.right.right gc
            simp only [this, true_implies, gt_iff_lt, isEmpty_Prop, not_lt, IsEmpty.forall_iff, and_true] at ind3
            rename_i g0 ; rw[g0, ind3, gt]
            have ind1:= indt1.left; unfold is_LCS_length at ind1; obtain ⟨s, ind1⟩ := ind1.right
            use s; simp only [ind1, contains_substring_cons, and_self]
          . have ind2:= indt1.right.left;
            rename_i gh g0 gc; rw[not_not] at gc; have ind2:= ind2 gc
            obtain ⟨pre, gc⟩ := gc; simp only [ne_eq, Decidable.not_not] at gh; rw[gh]
            use h2::pre; simp only [contains_substring, isPrefixOf_cons₂_self, IsPrefix_isPrefixOf_EQ, gc,
              ↓reduceIte, length_cons, true_and];
            rw[g0, ind2];
            have: pre.length = lct := is_LCS_length_unique pre.length lct gc.right.right indt1.left
            omega
  simp only [glc, true_and]
  --prove support Prop 1
  constructor
  . intro gp;
    simp only [LCS_length_aux, ne_eq, ite_not]
    split
    . rename_i gh; simp only [gh, ne_eq, not_true_eq_false, ↓reduceIte, zero_add] at g
      by_cases (∃ pre, pre <+: t1 ∧ pre <+: t2 ∧ is_LCS_length t1 t2 pre.length)
      . rename_i gc
        have gp1:= lcp_is_LCS_length gp glc; have gp2:= lcp_is_LCS_length gc indt1.left;
        simp only [LCP_length, gh, ne_eq, not_true_eq_false, ↓reduceIte] at gp1
        have e2:= indtp1.right.left gc
        have: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≤ LCS_length_aux t1 t2 (k + 1) := by omega
        simp only [this, max_eq_right]; omega
      . rename_i gc
        have e1 := sup_LCS_correct2 gp gc glc indt1.left
        have e2:= (indt1.right.right gc).left (by omega)
        by_cases (k + 1 + LCP_length t1 t2 ≤ lct)
        . rename_i gp1
          have e1:= (indtp1.right.right gc).left gp1
          have e3: k = 0 := by omega
          rw[e1, ← e2, gh, g, e3]; simp only [zero_add]
        . rename_i gp1; simp only [not_le] at gp1
          have e1:= (indtp1.right.right gc).right gp1
          have : (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≤ LCS_length_aux t1 t2 (k + 1) := by omega
          simp only [this, max_eq_right]; omega
    . rename_i gh;
      simp only [ne_eq, gh, not_false_eq_true, not_sym, ↓reduceIte, le_max_iff, _root_.zero_le, or_self, max_eq_left] at g
      obtain⟨pre, gp⟩:=gp
      cases pre
      . simp only [_root_.nil_prefix, length_nil, true_and] at gp
        have e:= is_LCS_length_unique lc 0 glc gp
        simp only [g, e, _root_.zero_le, max_eq_right, add_zero];
      . simp only [← IsPrefix_isPrefixOf_EQ, isPrefixOf, Bool.and_eq_true, beq_iff_eq,
        length_cons] at gp
        rw[← gp.left.left, ← gp.right.left.left] at gh; contradiction
  --prove support Prop 2
  . intro gp
    simp only [LCP_length, ne_eq, ite_not, LCS_length_aux, le_max_iff, _root_.zero_le, or_self, max_eq_left,
      zero_add, gt_iff_lt]
    split
    . rename_i gh; simp only [gh, ne_eq, not_true_eq_false, ↓reduceIte, zero_add] at g
      have := sup_LCS_correct1 gh gp
      have indtp1:= indtp1.right.right this
      have indt1:= (indt1.right.right this).left
      constructor
      . intro glcp
        cases e0
        . have e1:= indtp1.left (by omega)
          have e2:= indt1 (by omega)
          rw[e1,← e2]
        . have e2:= (indtp.right.right this).left (by omega)
          have i1:= @LCP_length_aux_para1_add1_le t1 t2 k
          have i2 := LCP_length_ne_LCS_length this indtp.left
          have indt1:= indt1 (by omega)
          have i3: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≥ LCS_length_aux t1 t2 1 :=by omega
          rw[gh] at i3; simp only [i3, max_eq_left] at g
          have i4: (LCS_length_aux (h2 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≥ LCS_length_aux t1 t2 (k+1) :=by omega
          rw[gh]; simp only [i3, i4, max_eq_left]
      . intro glcp
        have indtp1:= indtp1.right (by omega)
        have: (LCS_length_aux (h1 :: t1) t2 0).max (LCS_length_aux t1 (h2 :: t2) 0) ≤ LCS_length_aux t1 t2 (k + 1):= by omega
        simp only [this, max_eq_right]; omega
    . rename_i gh; simp only [ne_eq, gh, not_false_eq_true, not_sym, ↓reduceIte, le_max_iff,
      _root_.zero_le, or_self, max_eq_left] at g
      constructor
      . intro g0; simp only [add_zero, ← g, le_max_iff] at g0
        simp only [le_max_iff, g0, max_eq_left]
      . intro g0; simp only [add_zero] at g0; have g0:=le_of_lt g0
        rw[g]; simp only [g0, max_eq_right, add_zero]

theorem LCS_length_correct: LCS_length s1 s2  = l ↔ is_LCS_length s1 s2 l :=by
  apply mpr_of_unique _ is_LCS_length_unique
  intro l g; exact (@LCS_length_correct_mp s1 s2 l 1 g).left

