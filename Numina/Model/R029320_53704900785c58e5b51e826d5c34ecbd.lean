import Mathlib

theorem algebra_189554 (x : ℝ) (hx : x > 0) : x ^ (2 + Real.logb 10 x) = 100 * x ↔ x = 0.01 ∨ x = 10 := by
  constructor
  · -- Assume x^(2 + logb 10 x) = 100 * x, prove x = 0.01 ∨ x = 10
    intro h_eq
    have h1 : 0 < x := hx
    have h2 : Real.logb 10 (x ^ (2 + Real.logb 10 x)) = Real.logb 10 (100 * x) := by
      rw [h_eq]
    have h3 : Real.logb 10 (x ^ (2 + Real.logb 10 x)) = (2 + Real.logb 10 x) * Real.logb 10 x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        try linarith
        try tauto
    have h4 : Real.logb 10 (100 * x) = Real.logb 10 (100 : ℝ) + Real.logb 10 x := by
      rw [Real.logb_mul (by norm_num) (by linarith)]
    rw [h3] at h2
    rw [h4] at h2
    have h5 : Real.logb 10 (100 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h5] at h2
    have h6 : (Real.logb 10 x) ^ 2 + Real.logb 10 x - 2 = 0 := by
      nlinarith
    have h7 : (Real.logb 10 x - 1) * (Real.logb 10 x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case logb 10 x = 1
      have h10 : Real.logb 10 x = 1 := by linarith
      have h11 : x = (10 : ℝ) := by
        have h12 : x = (10 : ℝ) ^ (Real.logb 10 x : ℝ) := by
          rw [Real.rpow_logb]
          all_goals
            norm_num
            all_goals linarith
        rw [h10] at h12
        norm_num at h12 ⊢
        linarith
      right
      linarith
    · -- Case logb 10 x = -2
      have h13 : Real.logb 10 x = -2 := by linarith
      have h14 : x = (10 : ℝ) ^ (-2 : ℝ) := by
        have h15 : x = (10 : ℝ) ^ (Real.logb 10 x) := by
          field_simp [Real.rpow_logb, hx]
        rw [h13] at h15
        linarith
      have h15 : x = (0.01 : ℝ) := by
        rw [h14]
        norm_num
      left
      linarith
  · -- Assume x = 0.01 ∨ x = 10, prove x^(2 + logb 10 x) = 100 * x
    rintro (h_eq | h_eq)
    · -- Case x = 0.01
      rw [h_eq]
      have h1 : Real.logb 10 (0.01 : ℝ) = -2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h1]
      norm_num
    · -- Case x = 10
      rw [h_eq]
      have h1 : Real.logb 10 (10 : ℝ) = 1 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h1]
      norm_num