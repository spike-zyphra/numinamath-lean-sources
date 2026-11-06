import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_63004 (x y : ℝ) :
  sin ((x + y) / 2) = 0 ∧ abs x + abs y = 1 ↔
  (x = 1 / 2 ∧ y = -1 / 2) ∨ (x = -1 / 2 ∧ y = 1 / 2) := by
  constructor
  · -- Forward direction: both equations hold implies the two solutions
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : sin ((x + y) / 2) = 0 := h1
    have h4 : ∃ k : ℤ, (x + y) / 2 = k * Real.pi := by 
      rw [sin_eq_zero_iff] at h3
      rcases h3 with ⟨k, hk⟩
      refine ⟨k, by linarith [hk]⟩
    rcases h4 with ⟨k, hk⟩ 
    have eq1 : x + y = 2 * (k : ℝ) * Real.pi := by 
      linarith [hk]
    -- Add bounds on x + y from |x| + |y| = 1 
    have h5 : -2 ≤ x + y := by 
      cases' abs_cases x with hx hx <;> 
      cases' abs_cases y with hy hy <;> 
      linarith 
    have h6 : x + y ≤ 2 := by 
      cases' abs_cases x with hx hx <;> 
      cases' abs_cases y with hy hy <;> 
      linarith 
    -- Show k=0 from bounded x+y
    have hk1 : k = 0 := by
      have h7 : k > -1 := by 
        by_contra h 
        push_neg at h 
        have h8 : k ≤ -1 := by
          omega 
        have h9 : k ≤ -1 := h8
        have h13 : x + y = 2 * (k : ℝ) * Real.pi := eq1
        have h13 : x + y = 2 * (k : ℝ) * Real.pi := eq1 
        have h9 : k ≤ -1 := h8 
        have hk5 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h9 
        have h15 : x + y ≤ -2 * Real.pi := by
          have h21 : x + y = 2 * (k : ℝ) * Real.pi := eq1 
          have hk5 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h9 
          nlinarith [Real.pi_pos] 
        nlinarith [show Real.pi > 0 by exact Real.pi_pos, h6, Real.pi_gt_three]
      have h8 : k < 1 := by 
        by_contra h 
        push_neg at h 
        have h8 : k ≥ 1 := by 
          omega 
        have h9 : k ≥ 1 := h8 
        have h13 : x + y = 2 * (k : ℝ) * Real.pi := eq1 
        have h9 : k ≥ 1 := h8 
        have hk5 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h9 
        have h15 : x + y ≥ 2 * Real.pi := by
          have h21 : x + y = 2 * (k : ℝ) * Real.pi := eq1 
          have hk5 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h9 
          nlinarith [Real.pi_pos] 
        nlinarith [show Real.pi > 0 by exact Real.pi_pos, h5, Real.pi_gt_three]
      omega 
    have hx1 : x + y = 0 := by
      rw [hk1] at eq1
      simp at eq1 
      linarith 
    by_cases h5 : x ≥ 0 
    · -- If x >= 0 
      by_cases h6 : y ≥ 0 
      · -- If x >= 0 and y >= 0 
        have h7 : abs x = x := abs_of_nonneg h5 
        have h8 : abs y = y := abs_of_nonneg h6 
        have eq2 : x + y = 1 := by 
          linarith [h2, h7, h8] 
        nlinarith [hx1, eq2]
      · -- If x >= 0 and y < 0 
        have h7 : abs x = x := abs_of_nonneg h5 
        have h8 : abs y = -y := abs_of_neg (lt_of_not_ge h6) 
        have eq2 : x - y = 1 := by 
          linarith [h2, h7, h8]
        have hx : x = 1 / 2 := by
          linarith 
        have hy : y = -1 / 2 := by
          linarith 
        left 
        exact ⟨hx, hy⟩ 
    · -- If x < 0 
      by_cases h6 : y ≥ 0 
      · -- If x < 0 and y >= 0 
        have h7 : abs x = -x := abs_of_neg (lt_of_not_ge h5)
        have h8 : abs y = y := abs_of_nonneg h6 
        have eq2 : -x + y = 1 := by 
          linarith [h2, h7, h8]
        have hx : x = -1 / 2 := by 
          linarith 
        have hy : y = 1 / 2 := by
          linarith 
        right 
        exact ⟨hx, hy⟩ 
      · -- If x < 0 and y < 0 
        have h7 : abs x = -x := abs_of_neg (lt_of_not_ge h5)
        have h8 : abs y = -y := abs_of_neg (lt_of_not_ge h6) 
        have eq2 : -x - y = 1 := by 
          linarith [h2, h7, h8] 
        nlinarith 
  · -- Backward implication: each of the two solutions satisfies the conditions
    rintro (h | h)
    · -- First solution 
      rcases h with ⟨hx, hy⟩ 
      constructor 
      · -- Show sin ((x + y) / 2) = 0 
        rw [hx, hy] 
        norm_num 
      · -- Show abs x + abs y = 1 
        rw [hx, hy]
        norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Second solution
      rcases h with ⟨hx, hy⟩ 
      constructor 
      · -- Show sin ((x + y) / 2) = 0 
        rw [hx, hy] 
        norm_num 
      · -- Show abs x + abs y = 1 
        rw [hx, hy]
        norm_num [abs_of_nonneg, abs_of_nonpos]