import Mathlib

theorem algebra_13901 {x : ℝ} (hx : x > 2) :
    Real.logb 5 (x - 2) + Real.logb (Real.sqrt 5) (x^3 - 2) + Real.logb (1 / 5) (x - 2) = 4 ↔ x = 3 := by
  constructor
  · -- Assume the equation holds, prove x = 3
    intro h_eq
    have h1 : Real.logb (Real.sqrt 5) (x^3 - 2) = 2 * Real.logb 5 (x^3 - 2) := by
      have h2 : Real.logb (Real.sqrt 5) (x^3 - 2) = (Real.logb 5 (x^3 - 2)) / (Real.logb 5 (Real.sqrt 5)) := by 
        field_simp [Real.logb]
      have h3 : Real.logb 5 (Real.sqrt 5) = 1 / 2 := by
        have h4 : Real.sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by 
          rw [Real.sqrt_eq_rpow]
        rw [h4]
        have h5 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by 
          rw [Real.logb_rpow]
          all_goals norm_num
        linarith
      rw [h2, h3]
      <;> field_simp <;> ring
    have h2 : Real.logb (1 / 5) (x - 2) = - Real.logb 5 (x - 2) := by
      have h3 : Real.logb (1 / 5) (x - 2) = (Real.logb 5 (x - 2)) / (Real.logb 5 (1 / 5)) := by 
        field_simp [Real.logb]
      have h4 : Real.logb 5 (1 / 5) = -1 := by
        have h5 : Real.logb 5 (1 / 5) = Real.logb 5 1 - Real.logb 5 5 := by 
          field_simp [Real.logb_div]
        have h6 : Real.logb 5 1 = 0 := by 
          simp [Real.logb_one]
        have h7 : Real.logb 5 5 = 1 := by 
          norm_num [Real.logb_eq_iff_rpow_eq]
        rw [h5, h6, h7]
        <;> norm_num
      rw [h3, h4]
      <;> field_simp
    rw [h1, h2] at h_eq
    have h3 : Real.logb 5 (x^3 - 2) = 2 := by 
      have eq1 : Real.logb 5 (x - 2) + 2 * Real.logb 5 (x^3 - 2) - Real.logb 5 (x - 2) = 4 := by
        linarith [h_eq]
      have eq2 : 2 * Real.logb 5 (x^3 - 2) = 4 := by
        linarith [eq1]
      linarith
    have h4 : x^3 - 2 = (5 : ℝ) ^ (2 : ℝ) := by
      have h5 : Real.logb 5 (x^3 - 2) = 2 := h3
      rw [Real.logb_eq_iff_rpow_eq] at h5
      · linarith
      all_goals
      have h6 : x^3 - 2 > 0 := by
        have h51 : x > 2 := hx
        nlinarith [sq_nonneg (x^2), sq_nonneg (x + 2), sq_nonneg (x - 2)]
      all_goals nlinarith
    have h5 : x^3 - 2 = (25 : ℝ) := by
      norm_num at h4 ⊢
      linarith
    have h6 : x^3 = (27 : ℝ) := by
      linarith
    have h7 : x = 3 := by
      have h8 : x^3 - 27 = 0 := by
        nlinarith
      have h9 : (x - 3) * (x^2 + 3 * x + 9) = 0 := by
        ring_nf at h8 ⊢
        linarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- h10 : x - 3 = 0 
        linarith
      · -- h11 : x^2 + 3 * x + 9 = 0 
        have h12 : x^2 + 3 * x + 9 > 0 := by 
          nlinarith [sq_nonneg (x + 3 / 2)]
        nlinarith
    exact h7
  · -- Assume x = 3, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.logb (Real.sqrt 5) (3 ^ 3 - 2) = 2 * Real.logb 5 (3 ^ 3 - 2) := by
      have h2 : Real.logb (Real.sqrt 5) (3 ^ 3 - 2) = (Real.logb 5 (3 ^ 3 - 2)) / (Real.logb 5 (Real.sqrt 5)) := by 
        field_simp [Real.logb]
      have h3 : Real.logb 5 (Real.sqrt 5) = 1 / 2 := by
        have h4 : Real.sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h4]
        have h5 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by 
          rw [Real.logb_rpow]
          all_goals norm_num
        linarith
      rw [h2, h3]
      <;> field_simp <;> ring
    have h2 : Real.logb (1 / 5) (3 - 2) = - Real.logb 5 (3 - 2) := by
      have h3 : Real.logb (1 / 5) (3 - 2) = (Real.logb 5 (3 - 2)) / (Real.logb 5 (1 / 5)) := by 
        field_simp [Real.logb]
      have h4 : Real.logb 5 (1 / 5) = -1 := by
        have h5 : Real.logb 5 (1 / 5) = Real.logb 5 1 - Real.logb 5 5 := by 
          field_simp [Real.logb_div]
        have h6 : Real.logb 5 1 = 0 := by 
          simp [Real.logb_one]
        have h7 : Real.logb 5 5 = 1 := by 
          norm_num [Real.logb_eq_iff_rpow_eq]
        rw [h5, h6, h7]
        <;> norm_num
      rw [h3, h4]
      <;> field_simp
    rw [h1, h2]
    have h3 : Real.logb 5 (3 - 2) = 0 := by
      norm_num [Real.logb_eq_iff_rpow_eq]
    have h4 : Real.logb 5 (3 ^ 3 - 2) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h3, h4]
    all_goals norm_num