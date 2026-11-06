import Mathlib

theorem algebra_188217 (x : ℝ) (hx : x > 0) : x ^ (Real.logb 10 x) = 1000 * x ^ 2 ↔ x = 0.1 ∨ x = 1000 := by
  constructor
  · -- Assume x^(logb 10 x) = 1000 * x^2, prove x = 0.1 ∨ x = 1000
    intro h_eq
    have h1 : Real.logb 10 (x ^ (Real.logb 10 x)) = Real.logb 10 (1000 * x ^ 2) := by
      rw [h_eq]
    have h2 : Real.logb 10 (x ^ (Real.logb 10 x)) = (Real.logb 10 x) ^ 2 := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        try positivity
        try linarith
    have h3 : Real.logb 10 (1000 * x ^ 2) = Real.logb 10 (1000 : ℝ) + Real.logb 10 (x ^ 2 : ℝ) := by
      rw [Real.logb_mul (by positivity) (by positivity)]
      all_goals
        try positivity
        try linarith
    have h4 : Real.logb (10 : ℝ) (1000 : ℝ) = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h5 : Real.logb 10 (x ^ 2 : ℝ) = 2 * Real.logb 10 x := by
      simp [Real.logb_pow]
      all_goals
        try positivity
        try linarith
    have h6 : (Real.logb 10 x) ^ 2 - 2 * Real.logb 10 x - 3 = 0 := by
      rw [h2] at h1
      rw [h3, h4, h5] at h1
      nlinarith
    have h7 : (Real.logb 10 x - 3) * (Real.logb 10 x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case 1: Real.logb 10 x = 3, so x = 1000
      have h8' : Real.logb 10 x = (3 : ℝ) := by
        linarith
      have h10 : x = (10 : ℝ) ^ (3 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] at h8'
        · linarith
        all_goals linarith
      have h11 : x = (1000 : ℝ) := by
        norm_num at h10 ⊢
        linarith
      right
      norm_num at h11 ⊢
      linarith
    · -- Case 2: Real.logb 10 x = -1, so x = 0.1
      have h9' : Real.logb 10 x = (-1 : ℝ) := by
        linarith
      have h10 : x = (10 : ℝ) ^ (-1 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] at h9'
        · linarith
        all_goals linarith
      have h11 : x = (0.1 : ℝ) := by
        norm_num at h10 ⊢
        all_goals linarith
      left
      norm_num at h11 ⊢
      linarith
  · -- Assume x = 0.1 ∨ x = 1000, prove x ^ (Real.logb 10 x) = 1000 * x ^ 2
    rintro (h_eq | h_eq)
    · -- Case 1: x = 0.1
      rw [h_eq]
      have h1 : Real.logb (10 : ℝ) (0.1 : ℝ) = (-1 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        <;> linarith
      rw [h1]
      norm_num
    · -- Case 2: x = 1000
      rw [h_eq]
      have h1 : Real.logb (10 : ℝ) (1000 : ℝ) = (3 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        <;> linarith
      rw [h1]
      norm_num