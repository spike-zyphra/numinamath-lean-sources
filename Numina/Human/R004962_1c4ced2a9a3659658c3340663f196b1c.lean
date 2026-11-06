import Mathlib
open Polynomial Real

-- Define the cubic polynomial f(x) = 3x^3 - 13x^2 + 14x - 2
noncomputable def f_poly : Polynomial ℝ := 3 * Polynomial.X^3 - 13 * Polynomial.X^2 + 14 * Polynomial.X - 2

structure HasThreeDistinctRoots (f_poly : Polynomial ℝ) where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  hx0_eval : f_poly.eval x0 = 0
  hx1_eval : f_poly.eval x1 = 0
  hx2_eval : f_poly.eval x2 = 0
  hx0_ne_x1 : x0 ≠ x1
  hx0_ne_x2 : x0 ≠ x2
  hx1_ne_x2 : x1 ≠ x2

lemma l_eq_of_strictMonoOn_eq {l r a b: ℝ} {f : ℝ → ℝ}
    (hfsmono : StrictMonoOn f (Set.Ioo l r))
    (ha : a ∈ Set.Ioo l r) (hb : b ∈ Set.Ioo l r) (hab : f a = f b) :
    a = b := by
  rcases eq_or_ne a b with h | h
  . exact h
  . rcases lt_or_gt_of_ne h with h | h
    . apply hfsmono ha hb at h
      linarith only [h, hab]
    . rw [gt_iff_lt] at h
      apply hfsmono hb ha at h
      linarith only [h, hab]

-- Prove that the given factored expression equals f_poly
lemma eval_f_poly (x : ℝ) : x * (x - 2) * (3 * x - 7) - 2 = f_poly.eval x := by
  unfold f_poly
  simp
  ring_nf

-- Evaluate f(0) = -2
lemma f_eval_0 : f_poly.eval 0 = -2 := by
  rw [← eval_f_poly]
  norm_num

-- Evaluate f(1) = 2
lemma f_eval_1 : f_poly.eval 1 = 2 := by
  rw [← eval_f_poly]
  norm_num

-- Evaluate f(2) = -2
lemma f_eval_2 : f_poly.eval 2 = -2 := by
  rw [← eval_f_poly]
  norm_num

-- Evaluate f(3) = 4
lemma f_eval_3 : f_poly.eval 3 = 4 := by
  rw [← eval_f_poly]
  norm_num

-- f_poly is continuous as a polynomial over ℝ
lemma f_poly_continuous : Continuous f_poly.eval := by
  apply Polynomial.continuous

-- RootSet (converted to Finset) is a subset of the multiset of roots
lemma hh: (f_poly.rootSet ℝ).toFinset.card ≤ f_poly.roots.card := by
  simp [rootSet_def]
  simp [aroots]
  apply Multiset.toFinset_card_le

-- Confirm the degree of f_poly is 3 and it is not the zero polynomial
lemma f_poly_degree_and_non_zero : f_poly.natDegree = 3 ∧ f_poly ≠ 0 := by
  constructor
  .
    unfold f_poly
    compute_degree!
  .
    intro h_eq_zero
    have f_eval_1_val : f_poly.eval 1 = 2 := f_eval_1
    rw [h_eq_zero] at f_eval_1_val
    simp at f_eval_1_val

--Intermediate Value Theorem: if f changes sign over [a, b], there is a root in (a, b)
lemma root_exists_by_ivt (a b : ℝ) (ha_le_b : a ≤ b)
    (h_cont : ContinuousOn f_poly.eval (Set.Icc a b))
    (f_a_val : ℝ) (f_b_val : ℝ)
    (h_f_a : f_poly.eval a = f_a_val)
    (h_f_b : f_poly.eval b = f_b_val)
    (h_sign_change : f_a_val * f_b_val < 0) :
    ∃ x, f_poly.eval x = 0 ∧ a < x ∧ x < b := by
  by_cases h_f_a_neg : f_a_val < 0
  . 
    have h_f_b_pos : f_b_val > 0 := by
      apply mul_neg_iff.mp at h_sign_change
      rcases h_sign_change with (_ | _) <;> linarith
    have h_f_a_lt_f_b : f_a_val < f_b_val := by linarith
    have h_ivt_apply := intermediate_value_Ioo ha_le_b h_cont
    rw [h_f_a, h_f_b] at h_ivt_apply
    have h_zero_in_Ioo_vals : (0 : ℝ) ∈ Set.Ioo f_a_val f_b_val := by
      constructor
      . exact h_f_a_neg
      . exact h_f_b_pos
    have h_zero_in_image : (0 : ℝ) ∈ f_poly.eval '' (Set.Ioo a b) :=
      Set.mem_of_subset_of_mem h_ivt_apply h_zero_in_Ioo_vals
    rcases h_zero_in_image with ⟨x_root, hx_root_in_Ioo, h_eval_zero⟩
    exact ⟨x_root, h_eval_zero, hx_root_in_Ioo.left, hx_root_in_Ioo.right⟩
  . 
    have h_f_a_pos : f_a_val > 0 := by
      push_neg at h_f_a_neg 
      have h2 : f_a_val ≠ 0 := by
        by_contra h
        rw [h] at h_sign_change
        linarith
      by_contra h
      push_neg at h 
      have h2 : f_a_val = 0 := by linarith
      contradiction
    have h_f_b_neg : f_b_val < 0 := by
      apply mul_neg_iff.mp at h_sign_change
      rcases h_sign_change with (⟨ha_pos, hb_neg⟩ | ⟨ha_neg, hb_pos⟩) <;> linarith
    have h_f_b_lt_f_a : f_b_val < f_a_val := by linarith
    have h_ivt_apply' := intermediate_value_Ioo' ha_le_b h_cont
    rw [h_f_a, h_f_b] at h_ivt_apply'
    have h_zero_in_Ioo_vals' : (0 : ℝ) ∈ Set.Ioo f_b_val f_a_val := by
      constructor
      . exact h_f_b_neg
      . exact h_f_a_pos
    have h_zero_in_image : (0 : ℝ) ∈ f_poly.eval '' (Set.Ioo a b) :=
      Set.mem_of_subset_of_mem h_ivt_apply' h_zero_in_Ioo_vals'
    rcases h_zero_in_image with ⟨x_root, hx_root_in_Ioo, h_eval_zero⟩
    exact ⟨x_root, h_eval_zero, hx_root_in_Ioo.left, hx_root_in_Ioo.right⟩

-- Show existence of a root in (0, 1)
lemma exists_root_in_0_1 : ∃ x, f_poly.eval x = 0 ∧ 0 < x ∧ x < 1 := by
  have h_cont : ContinuousOn f_poly.eval (Set.Icc 0 1) :=
    Continuous.continuousOn f_poly_continuous
  have h_le : (0 : ℝ) ≤ 1 := by norm_num
  have h_ivt_apply := intermediate_value_Ioo h_le h_cont
  rw [f_eval_0, f_eval_1] at h_ivt_apply
  have h_zero_in_Ioo : (0 : ℝ) ∈ Set.Ioo (-2) 2 := by
    constructor <;> norm_num
  have h_zero_in_image : (0 : ℝ) ∈ f_poly.eval '' (Set.Ioo 0 1) :=
    Set.mem_of_subset_of_mem h_ivt_apply h_zero_in_Ioo
  rcases h_zero_in_image with ⟨x_root, hx_root_in_Ioo, h_eval_zero⟩
  exact ⟨x_root, h_eval_zero, hx_root_in_Ioo.left, hx_root_in_Ioo.right⟩

-- Show existence of a root in (1, 2)
lemma exists_root_in_1_2 : ∃ x, f_poly.eval x = 0 ∧ 1 < x ∧ x < 2 := by
  apply root_exists_by_ivt 1 2
  . norm_num 
  . apply Continuous.continuousOn f_poly_continuous 
  . exact f_eval_1
  . exact f_eval_2
  . norm_num

-- Show existence of a root in (2, 3)
lemma exists_root_in_2_3 : ∃ x, f_poly.eval x = 0 ∧ 2 < x ∧ x < 3 := by
  apply root_exists_by_ivt 2 3
  . norm_num 
  . apply Continuous.continuousOn f_poly_continuous 
  . exact f_eval_2
  . exact f_eval_3
  . norm_num

-- Use previous lemmas to construct three distinct real roots of f_poly
lemma distinct_roots_from_ivt : ∃ x0 x1 x2 : ℝ,
    f_poly.eval x0 = 0 ∧ 0 < x0 ∧ x0 < 1 ∧
    f_poly.eval x1 = 0 ∧ 1 < x1 ∧ x1 < 2 ∧
    f_poly.eval x2 = 0 ∧ 2 < x2 ∧ x2 < 3 ∧
    x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2 := by
  have ⟨x0_val, hx0_eval, hx0_pos, hx0_lt1⟩ := exists_root_in_0_1
  have ⟨x1_val, hx1_eval, hx1_gt1, hx1_lt2⟩ := exists_root_in_1_2
  have ⟨x2_val, hx2_eval, hx2_gt2, hx2_lt3⟩ := exists_root_in_2_3
  refine ⟨x0_val, x1_val, x2_val, hx0_eval, hx0_pos, hx0_lt1, hx1_eval, hx1_gt1, hx1_lt2, hx2_eval, hx2_gt2, hx2_lt3, ?_, ?_, ?_⟩
  . linarith [hx0_lt1, hx1_gt1]
  . linarith [hx0_lt1, hx2_gt2]
  . linarith [hx1_lt2, hx2_gt2]

-- Confirm the polynomial degree is 3
lemma deg_f_poly : Polynomial.natDegree f_poly = 3 := by
  unfold f_poly
  compute_degree!

-- Confirm f_poly is not zero
lemma poly_ne_zero : f_poly ≠ 0 := by
  intro h_eq_zero
  have h_eval_zero := Polynomial.ext_iff.mp h_eq_zero 0 
  have f_eval_1 : f_poly.eval 1 = 2 := by
    rw [← eval_f_poly]
    norm_num
  rw [h_eq_zero ] at f_eval_1   
  simp at f_eval_1

-- Show that a given set of three real roots is of cardinality 3 if they are distinct
lemma set_rst {r s t: ℝ} (hroots_distinct : r ≠ s ∧ r ≠ t ∧ s ≠ t): ({r, s, t} : Set ℝ).toFinset.card = 3 := by
  rw [Set.toFinset_insert, Set.toFinset_insert, Set.toFinset_singleton]
  rw [Finset.card_insert_of_not_mem]
  . rw [Finset.card_insert_of_not_mem]
    . rw [Finset.card_singleton]
    . simp
      exact hroots_distinct.2.2 
  . simp
    constructor
    . exact hroots_distinct.1
    . exact hroots_distinct.2.1

-- Show that the set {r, s, t} is a subset of the rootSet of f_poly
lemma subset_rst {r s t : ℝ} (hr' : f_poly.eval r = 0) (hs' : f_poly.eval s = 0)(ht' : f_poly.eval t = 0) : ({r, s, t} : Set ℝ) ⊆ (f_poly.rootSet ℝ) := by
  simp_rw [Set.subset_def]  
  intro x hx
  rcases hx with (hr | hs | ht)
  . rw [Polynomial.mem_rootSet]
    simp
    constructor
    . exact poly_ne_zero 
    . rw [hr]
      exact hr'
  . rw [Polynomial.mem_rootSet]
    simp
    constructor
    . exact poly_ne_zero 
    . rw [hs]
      exact hs'
  . rw [Polynomial.mem_rootSet]
    simp
    constructor
    . exact poly_ne_zero 
    . rw [ht]
      exact ht'

-- The next group of lemmas constructs and compares cardinalities and subsets

-- related to the rootSet and the roots found via the IVT above
lemma h_set_x0x1x2 {x0 x1 x2: ℝ}(hx0_ne_x1 : x0≠ x1)(hx0_ne_x2 : x0≠ x2)(hx1_ne_x2 : x1≠ x2) : ({x0, x1, x2} : Set ℝ).toFinset.card = 3 := by
  rw [Set.toFinset_insert, Set.toFinset_insert, Set.toFinset_singleton]
  rw [Finset.card_insert_of_not_mem]
  . rw [Finset.card_insert_of_not_mem]
    . rw [Finset.card_singleton]
    . rw [Finset.mem_singleton]
      exact hx1_ne_x2
  . simp
    constructor
    . exact hx0_ne_x1
    . exact hx0_ne_x2

lemma h_x_subset_root_set {x0 x1 x2}(hx0_eval : eval x0 f_poly = 0) (hx1_eval : eval x1 f_poly = 0)
    (hx2_eval : eval x2 f_poly = 0)  : ({x0, x1, x2} : Set ℝ) ⊆ (f_poly.rootSet ℝ) := by
  intro x hx
  rcases hx with (hr | hs | ht)
  . rw [Polynomial.mem_rootSet]
    simp
    constructor
    . exact poly_ne_zero 
    . rw [hr]
      exact hx0_eval
  . rw [Polynomial.mem_rootSet]
    simp
    constructor
    . exact poly_ne_zero 
    . rw [hs]
      exact hx1_eval 
  . rw [Polynomial.mem_rootSet]
    simp
    constructor
    . exact poly_ne_zero 
    . rw [ht]
      exact hx2_eval 

lemma h_x_subset_root_set_fin {x0 x1 x2}(hx0_eval : eval x0 f_poly = 0) (hx1_eval : eval x1 f_poly = 0)
    (hx2_eval : eval x2 f_poly = 0)  : ({x0, x1, x2} : Finset ℝ) ⊆ (f_poly.rootSet ℝ).toFinset := by
  rw [Set.subset_toFinset]
  have hh: Finset.toSet {x0, x1, x2} = {x0, x1, x2}:=by simp
  rw [hh]
  apply h_x_subset_root_set hx0_eval hx1_eval hx2_eval

lemma h_card_root_set {x0 x1 x2}(hx0_eval : eval x0 f_poly = 0) (hx1_eval : eval x1 f_poly = 0)
    (hx2_eval : eval x2 f_poly = 0)(hx0_ne_x1 : x0≠ x1)(hx0_ne_x2 : x0≠ x2)(hx1_ne_x2 : x1≠ x2): (f_poly.rootSet ℝ).toFinset.card = 3 := by
  apply le_antisymm
  . have hh: (f_poly.rootSet ℝ).toFinset.card ≤ f_poly.roots.card := by
      simp [rootSet_def]
      simp [aroots]
      apply Multiset.toFinset_card_le
    have hh2: f_poly.roots.card ≤ f_poly.natDegree := by
      apply Polynomial.card_roots'
    rw [deg_f_poly] at hh2
    exact Nat.le_trans hh hh2
  . rw [Finset.le_card_iff_exists_subset_card]
    use {x0, x1, x2}
    constructor
    . rw [Set.subset_toFinset]
      simp
      exact h_x_subset_root_set hx0_eval hx1_eval hx2_eval
    . have hh2 := h_set_x0x1x2 hx0_ne_x1 hx0_ne_x2 hx1_ne_x2
      simp at hh2
      exact hh2

lemma h_set_eq (h : HasThreeDistinctRoots f_poly)(hr' : f_poly.eval r = 0) (hs' : f_poly.eval s = 0)(ht' : f_poly.eval t = 0)(hroots_distinct : r ≠ s ∧ r ≠ t ∧ s ≠ t): ({r, s, t} : Set ℝ) = (f_poly.rootSet ℝ) := by
  apply Set.eq_of_subset_of_card_le
  . exact subset_rst hr' hs' ht'
  . simp
    have hh:=h_card_root_set h.hx0_eval h.hx1_eval h.hx2_eval h.hx0_ne_x1 h.hx0_ne_x2 h.hx1_ne_x2
    simp at hh
    rw [hh]
    have hh2:= set_rst hroots_distinct
    simp at hh2
    rw [hh2]

-- Prove that all roots r, s, t are positive
lemma roots_are_positive (r s t : ℝ) (hr' : f_poly.eval r = 0) (hs' : f_poly.eval s = 0)
    (ht' : f_poly.eval t = 0) (hroots_distinct : r ≠ s ∧ r ≠ t ∧ s ≠ t) :
    r > 0 ∧ s > 0 ∧ t > 0 := by
  obtain ⟨x0, x1, x2, hx0_eval, hx0_pos, hx0_lt1, hx1_eval, hx1_gt1, hx1_lt2, hx2_eval, hx2_gt2, hx2_lt3, hx0_ne_x1, hx0_ne_x2, hx1_ne_x2⟩ := distinct_roots_from_ivt
  have h_deg_f_poly : Polynomial.natDegree f_poly = 3 := deg_f_poly
  have h_f_poly_ne_zero : f_poly ≠ 0 := poly_ne_zero
  have h_set_rst : ({r, s, t} : Set ℝ).toFinset.card = 3 := set_rst hroots_distinct
  have h_subset_rst : ({r, s, t} : Set ℝ) ⊆ (f_poly.rootSet ℝ) := subset_rst hr' hs' ht'
  have h_set_x0x1x2 : ({x0, x1, x2} : Set ℝ).toFinset.card = 3 := h_set_x0x1x2 hx0_ne_x1 hx0_ne_x2 hx1_ne_x2
  have h_x_subset_root_set : ({x0, x1, x2} : Set ℝ) ⊆ (f_poly.rootSet ℝ) := h_x_subset_root_set hx0_eval hx1_eval hx2_eval
  have h_card_root_set : (f_poly.rootSet ℝ).toFinset.card = 3 := h_card_root_set hx0_eval hx1_eval hx2_eval hx0_ne_x1 hx0_ne_x2 hx1_ne_x2
  have h_set_eq : ({r, s, t} : Set ℝ) = (f_poly.rootSet ℝ) := by
    apply Set.eq_of_subset_of_card_le
    . exact h_subset_rst
    . simp
      simp at h_card_root_set
      rw [h_card_root_set]
      simp at h_set_rst
      rw [h_set_rst]
  have h_x_set_eq : ({x0, x1, x2} : Set ℝ) = (f_poly.rootSet ℝ) := by
    apply Set.eq_of_subset_of_card_le
    . exact h_x_subset_root_set
    . simp
      simp at h_set_x0x1x2
      rw [h_set_x0x1x2]
      simp at h_card_root_set
      rw [h_card_root_set]
  have h_final_set_eq : ({r, s, t} : Set ℝ) = ({x0, x1, x2} : Set ℝ) := by
    rw [h_set_eq, h_x_set_eq.symm]
  have h_x0_pos_val : x0 > 0 := hx0_pos
  have h_x1_pos_val : x1 > 0 := by linarith [hx1_gt1] 
  have h_x2_pos_val : x2 > 0 := by linarith [hx2_gt2] 
  have h_r_mem_set : r ∈ ({r, s, t} : Set ℝ) := by simp
  rw [h_set_eq] at h_r_mem_set
  rw [← h_x_set_eq] at h_r_mem_set
  simp at h_r_mem_set 
  let P (x : ℝ) := x > 0
  have h_x_set_all_pos : ∀ y ∈ ({x0, x1, x2} : Set ℝ), P y := by
    intro y hy
    simp at hy
    rcases hy with (rfl | rfl | rfl)
    . exact hx0_pos
    . exact h_x1_pos_val
    . exact h_x2_pos_val
  have h_rst_set_all_pos : ∀ z ∈ ({r, s, t} : Set ℝ), P z := by
    intro z hz
    apply h_x_set_all_pos z
    rwa [h_final_set_eq] at hz
  constructor
  . exact h_rst_set_all_pos r (by simp)
  . constructor
    . exact h_rst_set_all_pos s (by simp)
    . exact h_rst_set_all_pos t (by simp)

-- Prove the multiset of roots equals {r, s, t}
lemma roots_multiset_eq_of_distinct_real_roots (r s t : ℝ) (hr' : f_poly.eval r = 0) (hs' : f_poly.eval s = 0) (ht' : f_poly.eval t = 0)
    (hroots_distinct : r ≠ s ∧ r ≠ t ∧ s ≠ t) :
    f_poly.roots = ({r, s, t} : Multiset ℝ) := by
  have hss := f_poly_degree_and_non_zero
  have h_deg := hss.1
  have h_ne_zero := hss.2
  have hr_mem_rootSet : r ∈ f_poly.rootSet ℝ := by simp [Polynomial.mem_rootSet, h_ne_zero, hr']
  have hs_mem_rootSet : s ∈ f_poly.rootSet ℝ := by simp [Polynomial.mem_rootSet, h_ne_zero, hs']
  have ht_mem_rootSet : t ∈ f_poly.rootSet ℝ := by simp [Polynomial.mem_rootSet, h_ne_zero, ht']
  have h_set_card : ({r, s, t} : Set ℝ).toFinset.card = 3 := by
    simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
    simp_all only [ne_eq, not_false_eq_true, and_self, Finset.mem_insert, Finset.mem_singleton, or_self,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd]
  have h_subset : ({r, s, t} : Set ℝ) ⊆ f_poly.rootSet ℝ := by
    intro x hx
    simp at hx
    rcases hx with (rfl | rfl | rfl)
    . exact hr_mem_rootSet
    . exact hs_mem_rootSet
    . exact ht_mem_rootSet
  have h_rootSet_card_le_degree : (f_poly.rootSet ℝ).toFinset.card ≤ f_poly.natDegree := by
    have hh:=f_poly.card_roots'
    have hh2:(f_poly.rootSet ℝ).toFinset.card ≤ f_poly.roots.card:= by
      simp [rootSet_def]
      simp [aroots]
      apply Multiset.toFinset_card_le
    exact Nat.le_trans hh2 hh
  have h_rootSet_card_eq_3 : (f_poly.rootSet ℝ).toFinset.card = 3 := by
    apply le_antisymm
    . rwa [h_deg] at h_rootSet_card_le_degree
    . rw [Finset.le_card_iff_exists_subset_card]
      use {r, s, t}
      constructor
      . rw [Set.subset_toFinset]
        simp
        exact h_x_subset_root_set hr' hs' ht'
      . have hh2 := h_set_x0x1x2 hroots_distinct.1 hroots_distinct.2.1 hroots_distinct.2.2
        simp at hh2
        exact hh2
  have h_rootSet_card_eq_3_fin : f_poly.roots.card = 3 := by
    have hh2:(f_poly.rootSet ℝ).toFinset.card ≤ f_poly.roots.card:= by
      simp [rootSet_def]
      simp [aroots]
      apply Multiset.toFinset_card_le
    have hh:=f_poly.card_roots'
    apply le_antisymm
    rw [h_deg] at hh
    exact hh
    rw [h_rootSet_card_eq_3] at hh2
    exact hh2
  have h_set_eq : f_poly.rootSet ℝ = ({r, s, t} : Set ℝ) := by
    symm
    apply Set.eq_of_subset_of_card_le
    . exact h_subset
    . simp
      simp at h_rootSet_card_eq_3 h_set_card
      rw [h_rootSet_card_eq_3, h_set_card]
  have h_set_eq_fin : (f_poly.rootSet ℝ).toFinset = ({r, s, t} : Finset ℝ) := by
    simp_all only [ne_eq, not_false_eq_true, and_self, Set.mem_insert_iff, Set.mem_singleton_iff, or_self, or_false,
    or_true, Set.toFinset_insert, Set.toFinset_singleton, Finset.mem_insert, Finset.mem_singleton,
    Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, subset_refl, le_refl]
  unfold rootSet at h_set_eq_fin h_rootSet_card_eq_3 
  simp [aroots] at h_set_eq_fin h_rootSet_card_eq_3
  have h_roots_nodup : f_poly.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    rw [h_rootSet_card_eq_3,h_rootSet_card_eq_3_fin]
  have hhs : Multiset.Nodup (Multiset.ofList [r,s,t]):= by
    simp
    constructor
    constructor
    . exact hroots_distinct.1
    . exact hroots_distinct.2.1
    exact hroots_distinct.2.2
  have hh:=Multiset.Nodup.toFinset_inj h_roots_nodup hhs
  apply hh
  rw [h_set_eq_fin]
  simp

-- Apply Vieta's formulas to compute sum, pairwise products, and full product of roots
lemma sum_roots (r s t : ℝ) (hr' : f_poly.eval r = 0) (hs' : f_poly.eval s = 0) (ht' : f_poly.eval t = 0)
    (hroots_distinct : r ≠ s ∧ r ≠ t ∧ s ≠ t) : r + s + t = 13/3 := by
  have h4:f_poly.coeff 3 ≠ 0:= by
    unfold f_poly
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have hh:f_poly.natDegree = 3 := by
    compute_degree
    exact h4
    exact f_poly_degree_and_non_zero.1
  have h_leadingCoeff : f_poly.leadingCoeff = 3 := by
    rw [f_poly,leadingCoeff]
    unfold f_poly at hh
    rw [hh]
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have h_coeff_2 : f_poly.coeff 2 = -13 := by
    rw [f_poly]
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have hh2:=roots_multiset_eq_of_distinct_real_roots r s t hr' hs' ht' hroots_distinct
  have hroots : f_poly.roots.card = f_poly.natDegree := by simp [hh,hh2]
  have h2 : 2 ≤ f_poly.natDegree := by linarith
  have vieta_eq := Polynomial.coeff_eq_esymm_roots_of_card hroots h2
  rw [h_coeff_2, h_leadingCoeff,hh] at vieta_eq
  field_simp at vieta_eq
  simp at vieta_eq
  rw [hh2] at vieta_eq
  rw [Multiset.esymm,Multiset.powersetCard_one] at vieta_eq
  simp at vieta_eq
  nlinarith

lemma sum_prod_two_roots (r s t : ℝ) (hr' : f_poly.eval r = 0) (hs' : f_poly.eval s = 0) (ht' : f_poly.eval t = 0)
    (hroots_distinct : r ≠ s ∧ r ≠ t ∧ s ≠ t) : r * s + s * t + t * r = 14/3 := by
  have h4:f_poly.coeff 3 ≠ 0:= by
    unfold f_poly
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have hh:f_poly.natDegree = 3 := by
    compute_degree
    exact h4
    exact f_poly_degree_and_non_zero.1
  have h_leadingCoeff : f_poly.leadingCoeff = 3 := by
    rw [f_poly,leadingCoeff]
    unfold f_poly at hh
    rw [hh]
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have h_coeff_1 : f_poly.coeff 1 = 14 := by
    rw [f_poly]
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have hh2:=roots_multiset_eq_of_distinct_real_roots r s t hr' hs' ht' hroots_distinct
  have hroots : f_poly.roots.card = f_poly.natDegree := by simp [hh,hh2]
  have h1 : 1 ≤ f_poly.natDegree := by linarith
  have vieta_eq := Polynomial.coeff_eq_esymm_roots_of_card hroots h1
  rw [h_coeff_1, h_leadingCoeff,hh] at vieta_eq
  field_simp at vieta_eq
  rw [hh2] at vieta_eq
  rw [Multiset.esymm] at vieta_eq
  simp [Multiset.prod_cons, Multiset.sum_cons,Multiset.powersetCard_one] at vieta_eq
  nlinarith

lemma prod_roots (r s t : ℝ) (hr' : f_poly.eval r = 0) (hs' : f_poly.eval s = 0) (ht' : f_poly.eval t = 0)
    (hroots_distinct : r ≠ s ∧ r ≠ t ∧ s ≠ t) : r * s * t = 2/3 := by
  have h4:f_poly.coeff 3 ≠ 0:= by
    unfold f_poly
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have hh:f_poly.natDegree = 3 := by
    compute_degree
    exact h4
    exact f_poly_degree_and_non_zero.1
  have h_leadingCoeff : f_poly.leadingCoeff = 3 := by
    rw [f_poly,leadingCoeff]
    unfold f_poly at hh
    rw [hh]
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have h_coeff_0 : f_poly.coeff 0 = -2 := by
    rw [f_poly]
    simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_X]
  have hh2:=roots_multiset_eq_of_distinct_real_roots r s t hr' hs' ht' hroots_distinct
  have hroots : f_poly.roots.card = f_poly.natDegree := by simp [hh,hh2]
  have h0 : 0 ≤ f_poly.natDegree := by linarith
  have vieta_eq := Polynomial.coeff_eq_esymm_roots_of_card hroots h0
  rw [h_coeff_0, h_leadingCoeff,hh] at vieta_eq
  field_simp at vieta_eq
  rw [hh2] at vieta_eq
  rw [Multiset.esymm] at vieta_eq
  simp [Multiset.prod_cons, Multiset.sum_cons, Multiset.powersetCard_one] at vieta_eq
  nlinarith

-- Derive a formula for tan(arctan x + arctan y + arctan z) using identity
lemma tan_sum_three_arctan (x y z : ℝ) (h_xy_ne_one : 1 - x * y > 0)(h_denom_ne_zero : 1 - (x * y + y * z + z * x) > 0) :
    Real.tan (Real.arctan x + Real.arctan y + Real.arctan z)  =
    (x + y + z - x * y * z) / (1 - (x * y + y * z + z * x)) := by
  have hh := Real.arctan_add (show x * y<1 by linarith)
  have tan_sum_xy : Real.tan (Real.arctan x + Real.arctan y) = (x + y) / (1 - x * y) := by
    rw [hh]
    rw [Real.tan_arctan]
  have hs3 :((x + y) / (1 - x * y)) * z <1 := by
    have pos1 : 0 < 1 - x * y := by linarith
    have h1 : z * (x + y) < 1 - x * y := by linarith
    have h4 : (x + y) / (1 - x * y) * z = z * (x + y) / (1 - x * y) := by
      field_simp [show 1 - x * y ≠ 0 by linarith]
      <;> ring
    rw [h4]
    apply (div_lt_one (by linarith)).mpr
    linarith
  have hhh := Real.arctan_add (show ((x + y) / (1 - x * y)) * z <1 by exact hs3)
  rw [hh,hhh]
  rw [Real.tan_arctan]
  have h3 : 1 - x * y ≠ 0 := by linarith
  have h4 : 1 - (x * y + y * z + z * x) ≠ 0 := by linarith
  have h5 : (x + y) / (1 - x * y) + z = (x + y + z - x * y * z) / (1 - x * y) := by
    field_simp [h3]
    ring
  have h6 : 1 - (x + y) / (1 - x * y) * z = (1 - (x * y + y * z + z * x)) / (1 - x * y) := by
    field_simp [h3]
    ring
  rw [h5, h6]
  field_simp [h3, h4]

-- Handle multiple angle branches of arctan sum (up to multiples of π)
lemma my_arctan_add_cases (x y : ℝ) (h_ne_one : 1 - x * y ≠ 0) :
    ∃ (k : ℤ), Real.arctan x + Real.arctan y = Real.arctan ((x + y) / (1 - x * y)) + k * Real.pi := by
  by_cases h_lt_one : x * y < 1
  . 
    use 0
    rw [Real.arctan_add h_lt_one]
    ring
  . 
    have h_gt_one : x * y > 1 := by
      by_contra h
      push_neg at h
      have h_ge : x * y ≥ 1 := by
        by_contra h'
        push_neg at h'
        have h'' : x * y < 1 := by linarith
        exact h_lt_one h''
      have h_eq : x * y = 1 := by linarith [h, h_ge]
      have h_zero : (1 - x * y) = 0 := by
        rw [h_eq]
        norm_num
      contradiction
    by_cases hx_pos : x > 0
    . 
      use 1
      rw [Real.arctan_add_eq_add_pi h_gt_one hx_pos]
      field_simp
    . 
      have hx_neg : x < 0 := by
        by_contra h_not_neg_x 
        have h1 : x ≤ (0 : ℝ) := by
          by_contra h
          push_neg at h
          have : x > 0 := by linarith
          exact hx_pos this
        have h2 : x ≥ (0 : ℝ) := by
          by_contra h
          push_neg at h
          have : x < 0 := by linarith
          exact h_not_neg_x this
        have hz : x=0:= by linarith
        rw [hz] at h_gt_one
        simp at h_gt_one
        linarith
      use -1
      rw [Real.arctan_add_eq_sub_pi h_gt_one hx_neg]
      field_simp
      ring

-- More general tan sum identity considering possible kπ shifts
lemma tan_sum_three_arctan4 (x y z : ℝ) (h_xy_ne_one : 1 - x * y ≠ 0)
    (h_denom_ne_zero : 1 - (x * y + y * z + z * x) ≠ 0) :
    Real.tan (Real.arctan x + Real.arctan y + Real.arctan z)  =
    (x + y + z - x * y * z) / (1 - (x * y + y * z + z * x)) := by
  obtain ⟨k1, h_sum_xy⟩ := my_arctan_add_cases x y h_xy_ne_one
  rw [h_sum_xy]
  rw [add_assoc]
  have hh: arctan ((x + y) / (1 - x * y)) + (↑k1 * π + arctan z)=arctan ((x + y) / (1 - x * y)) + arctan z + ↑k1 * π:= by ring
  rw [hh]
  rw [Real.tan_add_int_mul_pi _ k1]
  let u := (x + y) / (1 - x * y)
  have h_u_mul_z_ne_one : 1 - u * z ≠ 0 := by
    field_simp [h_xy_ne_one] 
    unfold u
    have h3 : 1 - x * y ≠ 0 := h_xy_ne_one
    have h4 : 1 - (x * y + y * z + z * x) ≠ 0 := h_denom_ne_zero
    have h5 : (x + y) / (1 - x * y) + z = (x + y + z - x * y * z) / (1 - x * y) := by
      field_simp [h3]
      ring
    have h6 : 1 - (x + y) / (1 - x * y) * z = (1 - (x * y + y * z + z * x)) / (1 - x * y) := by
      field_simp [h3]
      ring
    rw [h6]
    field_simp [h3, h4]
  obtain ⟨k2, h_sum_uz⟩ := my_arctan_add_cases u z h_u_mul_z_ne_one
  rw [h_sum_uz]
  rw [Real.tan_add_int_mul_pi _ k2]
  rw [Real.tan_arctan]
  have numerator_simplified : u + z = (x + y + z - x * y * z) / (1 - x * y) := by
    unfold u
    field_simp [h_xy_ne_one] 
    ring 
  have denominator_simplified : 1 - u * z = (1 - (x * y + y * z + z * x)) / (1 - x * y) := by
    unfold u
    field_simp [h_xy_ne_one] 
    ring_nf
  rw [numerator_simplified, denominator_simplified]
  field_simp [h_xy_ne_one, h_denom_ne_zero]

-- arctan(x) bounds between 0 and π/2 if x > 0
lemma arctan_bounds_of_pos (x : ℝ) (hx_pos : x > 0) : 0 < Real.arctan x ∧ Real.arctan x < π / 2 := by
  constructor
  · 
    have h1 : Real.arctan 0 = 0 := by
      rw [Real.arctan_zero]
    have h2 : Real.arctan 0 < Real.arctan x := by
      apply Real.arctan_lt_arctan
      linarith
    linarith [h1, h2]
  · 
    have ht: Real.pi = π:= by simp
    rw [← ht]
    apply Real.arctan_lt_pi_div_two x

/- Show that the roots $r, s, t$ of the equation $x(x-2)(3 x-7)=2$ are real and positive. Find $\tan ^{-1} r$ $+\tan ^{-1} s+\tan ^{-1} t$. -/
theorem algebra_604824 (r s t : ℝ) (hr : r * (r - 2) * (3 * r - 7) = 2) 
    (hs : s * (s - 2) * (3 * s - 7) = 2) (ht : t * (t - 2) * (3 * t - 7) = 2)
    (hroots : r ≠ s ∧ r ≠ t ∧ s ≠ t) :
    r > 0 ∧ s > 0 ∧ t > 0 ∧ Real.arctan r + Real.arctan s + Real.arctan t = 3 * π / 4 := by
  have hr' : f_poly.eval r = 0 := by
    simp [f_poly]
    linarith
  have hs' : f_poly.eval s = 0 := by
    simp [f_poly]
    linarith
  have ht' : f_poly.eval t = 0 := by
    simp [f_poly]
    linarith
  have hh:= roots_multiset_eq_of_distinct_real_roots r s t hr' hs' ht' hroots
  have h_pos_roots : r > 0 ∧ s > 0 ∧ t > 0 := roots_are_positive r s t hr' hs' ht' hroots
  have h_sum_roots : r + s + t = 13/3 := sum_roots r s t hr' hs' ht' hroots
  have h_sum_prod_two_roots : r * s + s * t + t * r = 14/3 := sum_prod_two_roots r s t hr' hs' ht' hroots
  have h_prod_roots : r * s * t = 2/3 := prod_roots r s t hr' hs' ht' hroots
  have h_denom_ne_zero : 1 - (r * s + s * t + t * r) ≠ 0 := by
    rw [h_sum_prod_two_roots]
    norm_num
  have h_denom_ne_zero2 : 1 - r * s ≠ 0 := by
    by_contra h
    have h1 : r * s = 1 := by linarith 
    have ht : t = 2 / 3 := by 
      have h2 : r * s * t = 2 / 3 := h_prod_roots  
      rw [h1] at h2 
      nlinarith [h2]
    have h2 : r + s = 11 / 3 := by 
      have ht' : t = 2 / 3 := ht 
      have hsum' : r + s + t = 13 / 3 := h_sum_roots  
      rw [ht'] at hsum' 
      linarith
    have h3 : s * t + r * t = 11 / 3 := by 
      have h1' : r * s = 1 := h1 
      have hsumprod' : r * s + s * t + t * r = 14 / 3 := h_sum_prod_two_roots  
      nlinarith [hsumprod', h1']
    have h4 : s * t + r * t = t * (r + s) := by 
      ring
    have h5 : t * (r + s) = 22 / 9 := by 
      rw [ht, h2]
      norm_num 
    rw [h4] at h3 
    linarith [h3, h5]
  have h_tan_val : Real.tan (Real.arctan r + Real.arctan s + Real.arctan t) = -1 := by
    rw [tan_sum_three_arctan4 r s t h_denom_ne_zero2 h_denom_ne_zero]
    rw [h_sum_roots, h_prod_roots, h_sum_prod_two_roots]
    norm_num
  have h_arctan_r_bounds : 0 < Real.arctan r ∧ Real.arctan r < π / 2 := arctan_bounds_of_pos r h_pos_roots.1
  have h_arctan_s_bounds : 0 < Real.arctan s ∧ Real.arctan s < π / 2 := arctan_bounds_of_pos s h_pos_roots.2.1
  have h_arctan_t_bounds : 0 < Real.arctan t ∧ Real.arctan t < π / 2 := arctan_bounds_of_pos t h_pos_roots.2.2
  have h_sum_atan_bounds : 0 < Real.arctan r + Real.arctan s + Real.arctan t ∧
                           Real.arctan r + Real.arctan s + Real.arctan t < 3 * π / 2 := by
    constructor
    . apply add_pos
      apply add_pos
      exact h_arctan_r_bounds.left
      exact h_arctan_s_bounds.left
      exact h_arctan_t_bounds.left
    . linarith
  have h_final_value : Real.arctan r + Real.arctan s + Real.arctan t = 3 * π / 4 := by
    let x := arctan r + arctan s + arctan t
    have hx: x=arctan r + arctan s + arctan t := by simp
    rw [← hx] at h_sum_atan_bounds h_tan_val
    rw [← hx]
    have : 0 < x ∧ x < π := by
      by_contra h_contra
      rw [not_and_or] at h_contra
      rcases h_contra with h_contra | h_contra
      . tauto
      . rw [not_lt] at h_contra
        obtain ⟨h_pos, h_lt⟩ := h_sum_atan_bounds
        have : 0 ≤ tan x := by
          suffices : 0 ≤ tan (x - π)
          . rwa [tan_sub_pi] at this
          . apply tan_nonneg_of_nonneg_of_le_pi_div_two
            <;> linarith
        norm_num [h_tan_val] at this
    have h_mono := strictMonoOn_tan
    rw [StrictMonoOn] at h_mono
    have hy_tan : tan (x - π / 2) = 1 := by
      rw [show x - π / 2 = -(π / 2 - x) by ring, tan_neg,
          tan_pi_div_two_sub,
          h_tan_val]
      norm_num
    rw [← tan_pi_div_four] at hy_tan
    have h_y_bounds : x - π / 2 ∈ Set.Ioo (- (π / 2)) (π / 2) := by
      constructor <;> linarith
    suffices : x - π / 2 = π / 4
    . linarith only [this]
    . refine l_eq_of_strictMonoOn_eq strictMonoOn_tan h_y_bounds ?_ hy_tan
      rw [Set.mem_Ioo]
      constructor <;> linarith
  exact ⟨h_pos_roots.1,h_pos_roots.2.1,h_pos_roots.2.2, h_final_value⟩