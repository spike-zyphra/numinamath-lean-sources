import Mathlib

theorem algebra_223665 (x : ℝ) (hx : x^2 - 3 * x ≥ 0) :
    2 * x^2 - 3 * x = 2 * x * Real.sqrt (x^2 - 3 * x) + 1 ↔ x = -1 / 5 := by 
  constructor
  · -- First, prove the forward direction: if the equation holds, then x = -1/5
    intro h_eq 
    have h1 : Real.sqrt (x^2 - 3 * x) ≥ 0 := by 
      apply Real.sqrt_nonneg 
    have h2 : (Real.sqrt (x^2 - 3 * x)) ^ 2 = x^2 - 3 * x := by 
      rw [Real.sq_sqrt] 
      all_goals linarith 
    have eq1 : 2 * x^2 - 3 * x - 1 = 2 * x * Real.sqrt (x^2 - 3 * x) := by 
      nlinarith 
    have eq2 : (2 * x^2 - 3 * x - 1) ^ 2 = (2 * x * Real.sqrt (x^2 - 3 * x)) ^ 2 := by 
      rw [eq1] 
    have eq3 : (2 * x * Real.sqrt (x^2 - 3 * x)) ^ 2 = 4 * x^2 * (x^2 - 3 * x) := by 
      calc 
        (2 * x * Real.sqrt (x^2 - 3 * x)) ^ 2 
          = 4 * x^2 * (Real.sqrt (x^2 - 3 * x) ^ 2) := by 
            ring_nf 
        _ = 4 * x^2 * (x^2 - 3 * x) := by 
          rw [h2] 
    have eq4 : (2 * x^2 - 3 * x - 1) ^ 2 = 4 * x^2 * (x^2 - 3 * x) := by 
      rw [eq3] at eq2 
      linarith 
    have eq6 : 5 * x^2 + 6 * x + 1 = 0 := by
      nlinarith [sq_nonneg (x * (x + 1 / 5)), sq_nonneg ((x + 1 / 5) * (x + 1)), 
        sq_nonneg (2 * x^2 - 3 * x - 1), sq_nonneg (Real.sqrt (x^2 - 3 * x) - 4 / 5), 
        Real.sqrt_nonneg (x^2 - 3 * x), h2]
    have h3 : (5 * x + 1) * (x + 1) = 0 := by
      nlinarith [eq6] 
    cases' (mul_eq_zero.mp h3) with h4 h5 
    · -- Case 1: 5 * x + 1 = 0
      have hx1 : x = -1 / 5 := by 
        linarith 
      exact hx1 
    · -- Case 2: x + 1 = 0 
      have hx2 : x = -1 := by 
        linarith 
      have h_eq1 : 2 * x^2 - 3 * x = 2 * x * Real.sqrt (x^2 - 3 * x) + 1 := by 
        linarith 
      rw [hx2] at h_eq1 
      nlinarith [Real.sqrt_nonneg ((-1 : ℝ) ^ 2 - 3 * (-1)), Real.sq_sqrt (show ((-1 : ℝ) ^ 2 - 3 * (-1)) ≥ 0 by norm_num), Real.sqrt_le_sqrt (show ((-1 : ℝ) ^ 2 - 3 * (-1)) ≥ 0 by norm_num)]
  · -- Backward: x = -1/5 implies the equation 
    intro h_eq 
    rw [h_eq] 
    have h_sq3_25 : Real.sqrt ((-1 / 5 : ℝ) ^ 2 - 3 * (-1 / 5)) = (4 / 5 : ℝ) := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    rw [h_sq3_25] 
    norm_num