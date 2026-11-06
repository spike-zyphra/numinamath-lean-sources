import Mathlib

theorem algebra_167608 {x : ℝ} (hx : x > 1) :
    Real.logb 10 ((x - 1)^2)^4 + Real.logb 10 ((x - 1)^3)^2 = 25 ↔
    x = 1.1 ∨ x = 11 := by
  constructor
  · -- Assume the equation holds
    intro h_eq
    have h1 : Real.logb 10 ((x - 1) ^ 2) = 2 * Real.logb 10 (x - 1) := by
      have h2 : Real.logb 10 ((x - 1) ^ 2) = 2 * Real.logb 10 (x - 1) := by
        simp [Real.logb_pow]
      linarith [h2]
    have h2 : Real.logb 10 ((x - 1) ^ 3) = 3 * Real.logb 10 (x - 1) := by
      have h3 : Real.logb 10 ((x - 1) ^ 3) = 3 * Real.logb 10 (x - 1) := by
        simp [Real.logb_pow]
      linarith [h3]
    rw [h1] at h_eq
    rw [h2] at h_eq
    have h3 : (Real.logb 10 (x - 1)) ^ 2 = 1 := by
      nlinarith [sq_nonneg ((Real.logb 10 (x - 1)) ^ 2 - 1), sq_nonneg ((Real.logb 10 (x - 1)) ^ 2 + 1)]
    have h4 : Real.logb 10 (x - 1) = 1 ∨ Real.logb 10 (x - 1) = -1 := by
      have h5 : (Real.logb 10 (x - 1)) ^ 2 = 1 := h3
      have : Real.logb 10 (x - 1) = 1 ∨ Real.logb 10 (x - 1) = -1 := by
        rw [sq_eq_one_iff] at h5
        tauto
      tauto
    cases h4 with
    | inl h5 =>
      have h6 : x - 1 = 10 := by
        have h7 : x - 1 = (10 : ℝ) ^ (Real.logb 10 (x - 1) : ℝ) := by
          rw [Real.rpow_logb]
          all_goals
            linarith
        rw [h5] at h7
        norm_num at h7 ⊢
        linarith
      have h7 : x = 11 := by linarith
      right
      linarith
    | inr h5 =>
      have h6 : x - 1 = (0.1 : ℝ) := by
        have h7 : x - 1 = (10 : ℝ) ^ (Real.logb 10 (x - 1) : ℝ) := by
          rw [Real.rpow_logb]
          all_goals
            linarith
        rw [h5] at h7
        have h8 : (10 : ℝ) ^ (-1 : ℝ) = (0.1 : ℝ) := by
          norm_num
        rw [h8] at h7
        linarith
      have h7 : x = 1.1 := by
        nlinarith
      left
      linarith
  · -- Now the reverse direction
    rintro (h_eq | h_eq)
    · -- Case where x = 1.1
      rw [show x = 1.1 by linarith] 
      have h1 : Real.logb 10 ((1.1 - 1 : ℝ) ^ 2) = -2 := by
        have h2 : Real.logb 10 ((1.1 - 1 : ℝ) ^ 2) = 2 * Real.logb 10 (1.1 - 1 : ℝ) := by
          simp [Real.logb_pow]
        rw [h2]
        have h3 : Real.logb 10 (1.1 - 1 : ℝ) = -1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        rw [h3]
        all_goals norm_num
      have h2 : Real.logb 10 ((1.1 - 1 : ℝ) ^ 3) = -3 := by
        have h3 : Real.logb 10 ((1.1 - 1 : ℝ) ^ 3) = 3 * Real.logb 10 (1.1 - 1 : ℝ) := by
          simp [Real.logb_pow]
        rw [h3]
        have h4 : Real.logb 10 (1.1 - 1 : ℝ) = -1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        rw [h4]
        all_goals norm_num
      rw [h1, h2]
      all_goals norm_num
    · -- Case where x = 11
      rw [show x = 11 by linarith]
      have h1 : Real.logb 10 ((11 - 1 : ℝ) ^ 2) = 2 := by
        have h2 : Real.logb 10 ((11 - 1 : ℝ) ^ 2) = 2 * Real.logb 10 (11 - 1 : ℝ) := by
          simp [Real.logb_pow]
        rw [h2]
        have h3 : Real.logb 10 (11 - 1 : ℝ) = 1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        rw [h3]
        all_goals norm_num
      have h2 : Real.logb 10 ((11 - 1 : ℝ) ^ 3) = 3 := by
        have h3 : Real.logb 10 ((11 - 1 : ℝ) ^ 3) = 3 * Real.logb 10 (11 - 1 : ℝ) := by
          simp [Real.logb_pow]
        rw [h3]
        have h4 : Real.logb 10 (11 - 1 : ℝ) = 1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        rw [h4]
        all_goals norm_num
      rw [h1, h2]
      all_goals norm_num