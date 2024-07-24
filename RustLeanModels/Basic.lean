-- Copyright Kani Contributors
-- SPDX-License-Identifier: Apache-2.0 OR MIT
import Mathlib
open String
open List
open Mathlib
open Nat
set_option maxHeartbeats 10000000


--  library Defs
abbrev Str := List Char

--LOGIC

lemma exists_minima_prop_nat {p: Nat → Prop} : (∃ x , p x) → ∃ m, (p m) ∧ (∀ n, p n → m ≤ n) :=by
  intro gn; obtain ⟨n, gn⟩ := gn
  induction n using Nat.strong_induction_on
  rename_i n ind
  by_cases (∀ m < n, ¬ p m ); rename_i gm
  . exists n ; simp only [gn, true_and]; intro x gx ;
    by_contra; rename_i gc; simp only [not_le] at gc;
    have gm := gm x gc; contradiction
  . rename_i gm ; simp only [not_forall, not_not, exists_prop] at gm; obtain ⟨m,gm⟩:=gm
    have ind:= ind m gm.left gm.right ; obtain⟨x,gx⟩:= ind
    use x;

lemma imp_eq_not_or: (p → q) ↔  (¬ p ∨ q) :=by
  constructor ;
  intro g ; by_cases p;
  rename_i g1; simp only [g g1, g1, not_true_eq_false, false_or];
  rename_i g1; simp only [g1,not_false_eq_true, true_or]
  intro g; cases g; rename_i g1; simp only [g1, false_implies]; rename_i g1; simp only [g1, implies_true]

def unique {α : Type} (p: α → Prop) : Prop := ∀ x1 x2, p x1 → p x2 → x1 = x2

lemma unique_minima {p: Nat → Prop}: unique (fun x => p x ∧ (∀ y, p y → y ≥ x)) :=by
  unfold unique; intro x y g1 g2
  have := g1.right y g2.left
  have := g2.right x g1.left
  omega

lemma unique_maxima {p: Nat → Prop}: unique (fun x => p x ∧ (∀ y, p y → y ≤ x)) :=by
  unfold unique; intro x y g1 g2
  have := g1.right y g2.left
  have := g2.right x g1.left
  omega

theorem mpr_of_unique : (∀ y, (x = y) → p y) → unique p → (∀ y, ((x = y) ↔  p y)) := by
  intro g1 g2 y; constructor; exact g1 y; intro g3
  have g1:= g1 x; simp only [true_implies] at g1
  unfold unique at g2; exact g2 x y g1 g3

@[simp]
lemma not_sym :  ¬ x = y →  ¬ y = x := by intro g; by_contra; rename_i g1; symm at g1; contradiction

lemma exists_EQ {α: Type} {p q : α → Prop}: (∀ x, p x  ↔ q x) → ((∃ y, p y) ↔ (∃ y, q y)) :=by
  intro g; constructor
  intro gy ; obtain ⟨y,gy⟩ := gy ; rw[g y] at gy ; use y
  intro gy ; obtain ⟨y,gy⟩ := gy ; rw[← g y] at gy ; use y

lemma not_in_forall_not_eq {s: List α} (h: ∀ x ∈ s, a ≠ x) : a ∉ s :=by
  induction s; simp; rename_i head tail ind
  simp_all only [ne_eq, mem_cons, or_true, not_false_eq_true, implies_true, forall_const,
    forall_true_left, forall_eq_or_imp, not_sym, or_self]


-- NAT
lemma cases_max : x = Nat.max m n → (x=m) ∨ (x=n) :=by
  by_cases m ≤ n ; intro g; rename_i g0; simp only [g0, max_eq_right] at g; simp only [g, or_true]
  intro g; rename_i g0; simp only [not_le] at g0; have g0:= le_of_lt g0;
  simp only [g0, max_eq_left] at g; simp only [g, true_or]

lemma max_add_right : Nat.max a (b+c) ≤ c + Nat.max a b :=by
  by_cases a ≤ b ; rename_i g; simp only [g, max_eq_right, max_le_iff]; omega
  rename_i g; simp only [not_le] at g; have g:= le_of_lt g;
  simp only [g, max_eq_left, max_le_iff,le_add_iff_nonneg_left, _root_.zero_le, true_and, ge_iff_le]
  omega


lemma max_le_of_right_le: n ≤ k → Nat.max m n ≤ Nat.max m k := by
  intro g
  by_cases m ≤ n; rename_i g; simp only [g, max_eq_right, le_max_iff]; omega
  rename_i g; simp only [not_le] at g; have g:= le_of_lt g; simp only [g, max_eq_left, le_max_iff, le_refl, true_or]

lemma map_add_sub {l: List  Nat}:  List.map (fun x => x - c) (List.map (fun x => x + c) l) = l := by
  simp only [map_map]
  have : ((fun x => x - c) ∘ fun x => x + c) = (fun x => x) :=by
    ext x; simp only [Function.comp_apply, add_tsub_cancel_right]
  rw[this]; simp only [map_id']

lemma map_sub_add {l: List Nat} (g: ∀ x ∈ l, x ≥ c): List.map (fun x => x + c) (List.map (fun x => x - c) l) = l := by
  simp only [map_map]
  induction l; simp only [map_nil]
  rename_i h t ind
  simp only [map_cons, Function.comp_apply, cons.injEq]
  constructor;
  have: h ≥ c := by apply g; simp only [mem_cons, true_or]
  omega
  have: ∀ m ∈ t, m ≥ c := by simp only [mem_cons, ge_iff_le, forall_eq_or_imp] at g; exact g.right
  exact ind this

lemma map_add_comm {l: List Nat} : List.map (fun x => x + a) (List.map (fun x => x + b) l) = List.map (fun x => x + b) (List.map (fun x => x + a) l) :=by
  simp only [map_map, comp_add_right]; have: (a+b) = (b+a) := by omega
  rw[this]

lemma map_sub_comm : List.map (fun x: Nat=> x-a) (List.map (fun x=> x-b) l) = List.map (fun x=> x-b) (List.map (fun x=> x-a) l) :=by
  simp only [map_map];
  have: (fun x => x - a) ∘ (fun x => x - b) = (fun x => x - b) ∘ (fun x => x - a) :=by
    ext x; simp only [Function.comp_apply]; omega
  rw[this]

def list_nat_zero_to_aux (n:Nat) (i: Nat): List Nat := match n with
  | zero => []
  | succ t => i:: list_nat_zero_to_aux t (i+1)

def list_nat_zero_to (n:Nat):= list_nat_zero_to_aux n  0

def monotone (l: List Nat) := match l with
  |[] => true
  |h::t => (∀ m ∈ t, h ≤ m) ∧ monotone t

lemma map_sub_monotone: monotone l → monotone (List.map (fun x => x -k ) l) :=by
  induction l
  unfold monotone
  simp only [map_nil, forall_true_left] ;
  rename_i h t ind
  unfold monotone
  simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq, map_cons,
    mem_map, tsub_le_iff_right, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro g g1; simp only [ind g1, and_true]
  intro a ga ; have ga:= g a ga; omega

lemma map_add_monotone: monotone l → monotone (List.map (fun x => x + k ) l) :=by
  induction l
  unfold monotone
  simp only [map_nil, forall_true_left] ;
  rename_i h t ind
  unfold monotone
  simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq, map_cons,
    mem_map, tsub_le_iff_right, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro g g1; simp only [ind g1, and_true]
  intro a ga ; have ga:= g a ga; omega

lemma list_nat_zero_to_aux_para1_sub : list_nat_zero_to_aux n a = List.map (fun x => x - b) (list_nat_zero_to_aux n (a+b)):=by
  induction n generalizing a b
  simp only [list_nat_zero_to, list_nat_zero_to_aux, map_nil]
  rename_i n ind
  simp only [list_nat_zero_to_aux, map_cons, add_tsub_cancel_right, cons.injEq, true_and]
  have : a + b + 1 = (a + 1) + b:= by omega
  rw[this]; exact ind

lemma list_nat_zero_to_aux_para1_add : List.map (fun x => x + b) (list_nat_zero_to_aux n a) = (list_nat_zero_to_aux n (a+b)):=by
  induction n generalizing a b
  simp only [list_nat_zero_to, list_nat_zero_to_aux, map_nil]
  rename_i n ind
  simp only [list_nat_zero_to_aux, map_cons, add_tsub_cancel_right, cons.injEq, true_and]
  have : a + b + 1 = (a + 1) + b:= by omega
  rw[this]; exact ind

lemma list_nat_zero_to_aux_para1_elim :  List.map (fun x => x - i) (list_nat_zero_to_aux n i) = list_nat_zero_to n :=by
  have g:= @list_nat_zero_to_aux_para1_sub n 0 i; symm at g
  simp only [zero_add] at g; unfold list_nat_zero_to; exact g

lemma list_nat_zero_to_monotone : monotone (list_nat_zero_to n) :=by
  induction n
  simp only [list_nat_zero_to, list_nat_zero_to_aux, monotone]
  rename_i n ind
  simp only [list_nat_zero_to, list_nat_zero_to_aux, zero_add]
  unfold monotone; simp only [_root_.zero_le, implies_true, true_and, Bool.decide_eq_true]
  have i:=@list_nat_zero_to_aux_para1_add 1 n 0; simp only [zero_add] at i; rw[← i, ← list_nat_zero_to]
  apply map_add_monotone ind

lemma list_nat_zero_to_le : ∀ m ∈ (list_nat_zero_to n), m ≤ n :=by
  induction n
  simp only [list_nat_zero_to, list_nat_zero_to_aux, not_mem_nil, nonpos_iff_eq_zero, false_implies, implies_true]
  rename_i n ind
  simp only [list_nat_zero_to, list_nat_zero_to_aux, zero_add, mem_cons, forall_eq_or_imp, le_add_iff_nonneg_left,
    _root_.zero_le, true_and]
  have i:=@list_nat_zero_to_aux_para1_add 1 n 0; simp only [zero_add] at i; rw[← i, ← list_nat_zero_to]
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, add_le_add_iff_right]
  exact ind

lemma list_nat_zero_to_aux_ge : x ∈ list_nat_zero_to_aux n i → x ≥ i :=by
  induction n generalizing i
  simp only [list_nat_zero_to_aux, not_mem_nil, ge_iff_le, false_implies]
  simp only [list_nat_zero_to_aux, mem_cons, ge_iff_le]
  intro g; cases g; omega; rename_i n ind g; have ind:=ind g; omega

lemma list_nat_zero_to_aux_first_mem : list_nat_zero_to_aux n i = h::t → h = i :=by
  cases n
  simp only [list_nat_zero_to_aux, not_false_eq_true, not_sym, false_implies]
  simp only [list_nat_zero_to_aux, cons.injEq, and_imp]
  intro g _; omega

--LIST

lemma exist_last_mem : l.length > 0 → ∃ s c, l = s ++ [c] :=by
  generalize gr: reverse l = r
  cases r; simp only [reverse_eq_nil_iff] at gr; simp only [gr, length_nil, gt_iff_lt,
    lt_self_iff_false, nil_eq_append, and_false, not_false_eq_true, not_sym, exists_false,
    exists_const, IsEmpty.forall_iff]
  intro _g; rename_i h t ; use reverse t, h;
  have: reverse (reverse l) = reverse t ++ [h] := by simp only [gr, reverse_cons]
  simp only [reverse_reverse] at this; exact this

lemma length_pos_from_not_nil : s ≠ []  ↔  s.length > 0 := by
  constructor;
  intro g; by_contra; rename_i g0;
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at g0
  have g0:= eq_nil_of_length_eq_zero g0
  contradiction
  intro g; by_contra; rename_i g0; simp only [g0, length_nil, gt_iff_lt, lt_self_iff_false] at g

lemma getLast?_cons_cons : (h1::h2::t).getLast? = (h2::t).getLast? := by
  rw(config:={occs:= .pos [1]}) [getLast?] ;
  simp only; unfold getLast getLast?; simp only

lemma getLast?_cons_tail_ne_nil: t ≠ [] → (h::t).getLast? = t.getLast? :=by
  cases t; simp only [ne_eq, not_true_eq_false, dropLast_single, dropLast_nil, not_false_eq_true,
    not_sym, IsEmpty.forall_iff]
  simp only [ne_eq, not_false_eq_true, not_sym, forall_true_left]
  rw[List.getLast?_cons, List.getLast?_cons]
  simp only [getLastD_cons]

lemma dropLast_neq_nil :s1.length > 1 →  List.dropLast s1 = List.dropLast s2 → s2 ≠ []:= by
  cases s1; simp only [length_nil, gt_iff_lt, not_lt_zero', dropLast_nil, IsEmpty.forall_iff]
  rename_i h1 t1; cases t1; simp only [List.length_singleton, gt_iff_lt, lt_self_iff_false,
    dropLast_single, IsEmpty.forall_iff]
  simp only [length_cons, gt_iff_lt, one_lt_succ_succ, dropLast_cons₂, forall_true_left]
  cases s2; simp only [dropLast_nil, not_false_eq_true, not_sym, ne_eq, not_true_eq_false,
    IsEmpty.forall_iff]
  simp only [ne_eq, not_false_eq_true, not_sym, implies_true]

lemma dropLast_append_getLast : s = s.dropLast ++ [(s.getLast a)] :=by
  induction s; contradiction
  rename_i h t ind
  cases t; simp only [dropLast_single, getLast_singleton, List.nil_append]
  rename_i ht tt; simp only [dropLast_cons₂, cons_append, cons.injEq, true_and]
  have : ht :: tt ≠ [] :=by simp only [ne_eq, not_false_eq_true, not_sym]
  rw[getLast_cons' a this] ; apply ind


lemma reverse_iif {l1 l2 : List α}: l1 = l2 ↔ l1.reverse = l2.reverse :=by
  constructor; intro g; rw[g]
  intro g; rw[← @reverse_reverse _ l1, ← @reverse_reverse _ l2, g]

lemma reverse_change_side {l1 l2 : List α}: l1.reverse = l2 ↔ l1 = l2.reverse :=by
  rw[reverse_iif, reverse_reverse];


/-
PREFIX LEMMAs
-/


@[simp]
lemma self_prefix : List.IsPrefix s s :=by
  unfold List.IsPrefix; use [] ; simp only [List.append_nil]

@[simp]
lemma nil_prefix : List.IsPrefix [] s :=by apply List.nil_prefix

@[simp]
lemma head_prefix : List.IsPrefix [h] (h::t) :=by
  unfold List.IsPrefix; use t ; simp only [singleton_append]

lemma prefix_length_le (h: List.IsPrefix p s) : p.length ≤ s.length :=by
  unfold List.IsPrefix at h;
  obtain ⟨t, ht⟩ := h ;
  have i: s.length = p.length + t.length := by rw [← ht]; apply List.length_append
  linarith

lemma prefix_eq_self (h: List.IsPrefix p s) (hl: p.length = s.length) : p = s :=by
  unfold List.IsPrefix at h
  obtain ⟨t, ht⟩ := h
  have : p.length + t.length = s.length := by rw[← ht] ; symm; apply List.length_append
  simp_all only [add_right_eq_self] ;
  have : t =[] := by apply List.eq_nil_of_length_eq_zero this
  rw[this] at ht; simp_all only [List.append_nil, length_nil]

lemma prefix_eq_of_length_eq (h1: List.IsPrefix p1 s) (h2: List.IsPrefix p2 s)
  (hl: p1.length = p2.length) : p1 = p2 :=by
  have i1: List.IsPrefix p1 p2 := by apply List.prefix_of_prefix_length_le h1 h2 ; linarith
  apply prefix_eq_self i1 hl

lemma prefix_eq_take (h: List.IsPrefix p s) : s.take p.length = p := by
  have e1: List.IsPrefix (s.take p.length) s := by apply List.take_prefix
  have e2: (s.take p.length).length = min p.length s.length := by apply List.length_take
  have e3 := prefix_length_le h
  have e4: min p.length s.length = p.length :=by simp only [ge_iff_le, e3, min_eq_left]
  rw[e4] at e2
  apply prefix_eq_of_length_eq e1 h e2

@[simp]
lemma prefix_cons {α : Type} {hp hs : α} {tp ts : List α} :
  List.IsPrefix (hp::tp) (hs::ts) →  (hp = hs) ∧ (List.IsPrefix tp ts) :=by
  intro h
  unfold List.IsPrefix at h
  obtain ⟨q,hq⟩ := h
  simp only [cons_append, cons.injEq] at hq
  simp only [hq, true_and] ; unfold List.IsPrefix;  use q ; simp only [hq]


lemma prefix_cons_mpr  {u: Type} {tp ts: List u} (h: List.IsPrefix tp ts) (a:u)
      : (List.IsPrefix (a::tp) (a::ts)) :=by
  unfold List.IsPrefix at h
  obtain ⟨q,hq⟩ := h
  unfold List.IsPrefix; use q; simp only [cons_append, hq]

lemma prefix_map {p s: List Char}  (g: List.IsPrefix p s) (f: Char → Nat): List.IsPrefix (List.map f p)  (List.map f s) :=by
  induction s generalizing p
  simp only [prefix_nil] at g; simp only [g, map_nil, self_prefix]
  rename_i hs ts ind
  cases p; simp only [map_nil, map_cons, _root_.nil_prefix]
  rename_i hp tp
  have g := prefix_cons g
  simp only [map_cons, g];
  have := ind (g.right)
  apply (prefix_cons_mpr this (f hs))

lemma prefix_trans (g1: List.IsPrefix p s) (g2: List.IsPrefix s t) :  List.IsPrefix p t :=by
  unfold List.IsPrefix at g1 g2
  unfold List.IsPrefix
  obtain ⟨q,hq⟩ := g1
  obtain ⟨r,hr⟩ := g2
  use q++r;
  rw [← List.append_assoc]; rw[hq, hr]

lemma prefix_mem (g: List.IsPrefix p s) (g2: m ∈ p) : m ∈ s := by
  unfold List.IsPrefix at g; obtain ⟨q,hq⟩ := g
  rw[← hq] ; apply List.mem_append_left q g2

lemma prefix_append_or : List.IsPrefix (l1 ++ t1) (l2 ++ t2)
          → (List.IsPrefix l1 l2) ∨ (List.IsPrefix l2 l1) :=by
  intro h
  unfold List.IsPrefix at h
  obtain ⟨v, hv⟩ := h
  have p1: List.IsPrefix l1 (l2 ++ t2) := by
    unfold List.IsPrefix; use t1 ++ v ; rw[← hv]; simp
  have p2: List.IsPrefix l2 (l2 ++ t2) :=by simp
  apply List.prefix_or_prefix_of_prefix p1 p2

lemma IsPrefix_isPrefixOf_EQ {p : List Char} : List.isPrefixOf p l ↔  List.IsPrefix p l :=by
  constructor
  --mp
  intro h
  generalize hi: List.length l = i
  induction i generalizing l p
  have i1: l = [] :=by apply List.eq_nil_of_length_eq_zero; exact hi
  have i2: p = [] :=by
    unfold List.isPrefixOf at h;
    split at h; simp only; contradiction;
    simp_all only [length_nil, zero_eq, not_false_eq_true, not_sym]
  simp_all only [isPrefixOf_nil_left, length_nil, zero_eq, prefix_nil]
  rename_i n ind
  unfold List.IsPrefix
  unfold List.isPrefixOf at h; split at h
  use l; simp only [List.nil_append]
  contradiction
  rename_i a ais b bis
  have e1: a = b :=by simp_all only [length_cons, succ.injEq, Bool.and_eq_true, beq_iff_eq]
  rw[e1]
  have p1: List.isPrefixOf ais bis = true :=by simp_all only [length_cons, succ.injEq,
    beq_self_eq_true, Bool.true_and]
  have p2: bis.length =  n :=by simp_all only [length_cons, succ.injEq, beq_self_eq_true,
    Bool.and_self]
  have p3:= ind p1 p2
  unfold List.IsPrefix at p3
  obtain ⟨t, ht⟩ := p3
  use t; simp_all only [length_cons, beq_self_eq_true, Bool.and_self, cons_append]
  --mpr
  intro h
  generalize hi: List.length l = i
  induction i generalizing l p
  have i1: l = [] :=by apply List.eq_nil_of_length_eq_zero; exact hi
  have i2: p = [] :=by apply List.prefix_nil.mp; simp_all only [prefix_nil, length_nil, zero_eq]
  simp_all only [isPrefixOf_nil_left, length_nil, zero_eq, prefix_nil]
  rename_i n ind
  unfold List.IsPrefix at h
  unfold List.isPrefixOf ; split; simp only;
  simp_all only [imp_false, append_eq_nil, false_and, not_false_eq_true, not_sym, exists_const]
  rename_i a ais b bis
  have e1: a = b :=by
    simp_all only [length_cons, succ.injEq, cons_append, cons.injEq, exists_and_left]
  simp_all only [length_cons, succ.injEq, cons_append, cons.injEq, true_and, beq_self_eq_true,
    Bool.true_and]
  have p1: List.IsPrefix ais bis := h
  apply ind p1 hi

lemma prefix_append_drop : List.IsPrefix p s → s = p ++ (s.drop p.length) := by
  intro g; have i:= prefix_eq_take g;
  rw(config:={occs:=.pos [1]})[← i]; simp only [take_append_drop]


/-
SUFFIX LEMMAs
-/
lemma IsSuffix_isSuffixOf_EQ {p : List Char}: List.isSuffixOf p l ↔  List.IsSuffix p l := by
  rw[List.isSuffixOf, IsPrefix_isPrefixOf_EQ]
  rw[← List.reverse_suffix]; simp only [reverse_reverse]

lemma suffix_trans (g1: List.IsSuffix s2 s1) (g2: List.IsSuffix s1 s) :  List.IsSuffix s2 s :=by
  unfold List.IsSuffix at *
  obtain⟨t1,g1⟩:=g1; obtain⟨t2,g2⟩:=g2; rw[← g1, ← List.append_assoc] at g2; use t2++t1

lemma suffix_eq_drop (g: List.IsSuffix p s) : s.drop (s.length - p.length) = p := by
  unfold List.IsSuffix at g ; obtain ⟨t,g⟩:= g
  have : t = s.take (t.length) := by simp only [← g, take_left]
  simp only [← g, List.length_append, add_tsub_cancel_right, drop_left]

lemma take_append_suffix (g: List.IsSuffix p s): s = List.take (s.length - p.length) s ++ p:= by
  rw (config:={occs:=.pos [2]}) [← suffix_eq_drop g]
  simp only [take_append_drop]


/-
ZIP and UNZIP
-/

lemma unzip_s (gs: s= List.zip s1 s2):
  (s.unzip.2 = s2.take s.length) ∧  (s.unzip.1 = s1.take s.length) := by
  induction s generalizing s1 s2;
  simp only [unzip_nil, length_nil, take_zero, and_self]
  rename_i h t ind
  simp only [unzip_cons, length_cons]
  cases s1; cases s2
  simp only [zip_nil_right, not_false_eq_true, not_sym] at gs
  simp only [zip_nil_left, not_false_eq_true, not_sym] at gs
  cases s2
  simp only [zip_nil_right, not_false_eq_true, not_sym] at gs
  simp only [zip_cons_cons, cons.injEq] at gs
  simp_all only [length_zip, take_cons_succ, and_self]

lemma unzip_eq_left_shorter (gs: s= List.zip s1 s2) (gl: s1.length ≤ s2.length):
   s.unzip.1 = s1 := by
  have z := (unzip_s gs).right
  simp_all only [length_zip, ge_iff_le, min_eq_left, take_length]

lemma unzip_eq_right_shorter (gs: s= List.zip s1 s2) (gl: s2.length ≤ s1.length):
   s.unzip.2 = s2 := by
  have z := (unzip_s gs).left
  simp_all only [length_zip, ge_iff_le, min_eq_right, take_length]

lemma nil_zip_left (g: List.zip [a] b = []) : b = [] :=by
  unfold List.zip  at g
  have := List.zipWith_eq_nil_iff.mp g
  simp_all only [zipWith_eq_nil_iff, not_false_eq_true, not_sym, false_or, or_true]

lemma nil_zip_right (h: List.zip b [a] = []) : b = [] :=by
  unfold List.zip  at h
  have := List.zipWith_eq_nil_iff.mp h
  simp_all only [zipWith_eq_nil_iff, not_false_eq_true, not_sym, or_false]

lemma take_n {α: Type} {head : α} {tail: List α}:
  List.take (succ n) (head :: tail) = head:: List.take n tail:=by
    unfold List.take; simp
    generalize ht : List.take n tail = te
    unfold List.take at ht;
    simp [ht]

theorem zip_take_zip {α: Type} {β: Type} {a: List α} {b: List β}:
  (List.zip a b).take n  = List.zip (a.take n) (b.take n) :=by
  generalize hl: (List.zip a b) = s
  induction s generalizing a b n
  unfold List.zip at hl
  have hl:= List.zipWith_eq_nil_iff.mp hl
  cases hl;
  simp_all only [zipWith_nil_left, take_nil, zip_nil_left]
  simp_all only [zipWith_nil_right, take_nil, zip_nil_right]
  rename_i head tail ind
  cases a; simp_all only [zip_nil_left, not_false_eq_true, not_sym]
  cases b; simp_all only [zip_nil_right, not_false_eq_true, not_sym]
  rename_i ha ta hb tb
  have tab: List.zip ta tb = tail := by simp_all only [zip_cons_cons, cons.injEq]
  cases n; simp only [zero_eq, take_zero, zip_nil_right]
  rename_i n
  rw[take_n, take_n, take_n]
  rw[zip_cons_cons]
  rw[zip_cons_cons] at hl
  have hab: head = (ha, hb) :=by symm at hl; simp_all only [cons.injEq, and_true]
  simp only [hab, cons.injEq, true_and]
  apply ind tab

theorem unzip_take_eq_take_unzip :
  (List.unzip a).1.take n  = (List.unzip (a.take n)).1 :=by
  induction a generalizing n
  simp only [unzip_nil, take_nil]
  rename_i h t ind
  simp_all only [unzip_cons]
  cases n; simp only [zero_eq, take_zero, unzip_nil]
  rename_i n; unfold List.take
  simp_all only [unzip_cons, cons.injEq, true_and]

def option_eq (a: Option Char) (b: Char) : Bool := (a = some b)

def option_not_eq (a: Option Char) (b: Char) : Bool := match a with
  | none => true
  | some s => s ≠ b

lemma of_mem_unzip (g: m ∈ (List.unzip l).1) : ∃ n, (m,n) ∈ l := by
  induction l
  simp only [unzip_nil, List.not_mem_nil] at g
  rename_i h t ind
  simp at g;
  cases g; use h.2; simp_all only [Prod.mk.eta, mem_cons, true_or]
  rename_i h; have ind:=ind h
  obtain ⟨n, hn⟩ := ind
  use n; simp_all only [forall_true_left, mem_cons, or_true]

theorem unzip_zip_take_left : (List.unzip (List.zip a b)).1 = a.take (min a.length b.length) := by
  generalize hl: (List.zip a b) = s
  induction s generalizing a b
  simp_all only [unzip_nil]
  unfold List.zip at hl
  have hl:= List.zipWith_eq_nil_iff.mp hl
  cases hl;
  simp_all only [zipWith_nil_left, length_nil, ge_iff_le, _root_.zero_le, min_eq_left, take_nil]
  have: b.length = 0 :=by rename_i h; simp only [h, length_nil]
  simp only [this, ge_iff_le, _root_.zero_le, min_eq_right, take_zero]
  rename_i head tail ind
  cases a; simp only [zip_nil_left, not_false_eq_true, not_sym] at hl
  cases b; simp only [zip_nil_right, not_false_eq_true, not_sym] at hl
  rename_i ha ta hb tb
  have tab: tail = List.zip ta tb := by simp_all only [zip_cons_cons, cons.injEq]
  simp_all only [zip_cons_cons, cons.injEq, and_true, unzip_cons, length_cons]
  have tka: List.take (min (succ ta.length) (succ tb.length)) (ha :: ta)
    = ha::List.take (min ta.length tb.length) ta :=by
    unfold List.take
    have : min (succ ta.length) (succ tb.length) = succ (min ta.length tb.length)
      :=by apply succ_min_succ
    simp [this]
    generalize ht : List.take (min ta.length tb.length) ta = t
    unfold List.take at ht
    simp only [ht]
  rw[tka]
  have : head.1 = ha :=by symm at hl; simp only [hl]
  simp only [this, cons.injEq, true_and]
  apply ind; simp


theorem unzip_zip_take_right: (List.unzip (List.zip a b)).2 = b.take (min a.length b.length) := by
  generalize hl: (List.zip a b) = s
  induction s generalizing a b
  simp_all only [unzip_nil]
  unfold List.zip at hl
  have hl:= List.zipWith_eq_nil_iff.mp hl
  cases hl;
  simp_all only [zipWith_nil_left, length_nil, ge_iff_le, _root_.zero_le, min_eq_left, take_zero]
  have: b.length = 0 :=by rename_i h; simp only [h, length_nil]
  simp_all only [zipWith_nil_right, length_nil, ge_iff_le, _root_.zero_le, min_eq_right, take_nil]
  rename_i head tail ind
  cases a; simp only [zip_nil_left, not_false_eq_true, not_sym] at hl
  cases b; simp only [zip_nil_right, not_false_eq_true, not_sym] at hl
  rename_i ha ta hb tb
  have tab: tail = List.zip ta tb := by simp_all only [zip_cons_cons, cons.injEq]
  simp_all only [zip_cons_cons, cons.injEq, and_true, unzip_cons, length_cons]
  have tka: List.take (min (succ ta.length) (succ tb.length)) (hb :: tb)
    = hb::List.take (min ta.length tb.length) tb :=by
    unfold List.take
    have : min (succ ta.length) (succ tb.length) = succ (min ta.length tb.length)
      :=by apply succ_min_succ
    simp [this]
    generalize ht : List.take (min ta.length tb.length) tb = t
    unfold List.take at ht
    simp only [ht]
  rw[tka]
  have : head.2 = hb :=by symm at hl; simp only [hl]
  simp only [this, cons.injEq, true_and]
  apply ind; simp only
