import Mathlib

theorem algebra_165811 (x : ℝ) (hx : 0 ≤ 3 * x ^ 2 - 2 * x + 15) (hx' : 0 ≤ 3 * x ^ 2 - 2 * x + 8) :
    Real.sqrt (3 * x ^ 2 - 2 * x + 15) + Real.sqrt (3 * x ^ 2 - 2 * x + 8) = 7 ↔
    x = -1 / 3 ∨ x = 1 := by 
  constructor 
  · -- Assume the equation holds, prove x = -1/3 or 1 
    intro h_eq 
    have h1 : Real.sqrt (3 * x ^ 2 - 2 * x + 15) ≥ 0 := by positivity 
    have h2 : Real.sqrt (3 * x ^ 2 - 2 * x + 8) ≥ 0 := by positivity 
    have h3 : (Real.sqrt (3 * x ^ 2 - 2 * x + 15) + Real.sqrt (3 * x ^ 2 - 2 * x + 8)) ^ 2 = 49 := by
      rw [h_eq]
      norm_num 
    have h4 : (Real.sqrt (3 * x ^ 2 - 2 * x + 15)) ^ 2 = 3 * x ^ 2 - 2 * x + 15 := Real.sq_sqrt (by linarith)
    have h5 : (Real.sqrt (3 * x ^ 2 - 2 * x + 8)) ^ 2 = 3 * x ^ 2 - 2 * x + 8 := Real.sq_sqrt (by linarith)
    have h7 : Real.sqrt (3 * x ^ 2 - 2 * x + 15) * (Real.sqrt (3 * x ^ 2 - 2 * x + 8)) = -3 * x ^ 2 + 2 * x + 13 := by 
      nlinarith [h3, Real.sqrt_nonneg (3 * x ^ 2 - 2 * x + 15), Real.sqrt_nonneg (3 * x ^ 2 - 2 * x + 8), mul_nonneg (Real.sqrt_nonneg (3 * x ^ 2 - 2 * x + 15)) (Real.sqrt_nonneg (3 * x ^ 2 - 2 * x + 8))]
    have h9 : 3 * x ^ 2 - 2 * x - 1 = 0 := by 
      nlinarith [sq_nonneg (3 * x ^ 2 - 2 * x - 1), sq_nonneg (Real.sqrt (3 * x ^ 2 - 2 * x + 15) - Real.sqrt (3 * x ^ 2 - 2 * x + 8)), sq_nonneg (3 * x ^ 2 - 2 * x - 1), Real.sqrt_nonneg (3 * x ^ 2 - 2 * x + 15), Real.sqrt_nonneg (3 * x ^ 2 - 2 * x + 8), sq_nonneg (Real.sqrt (3 * x ^ 2 - 2 * x + 15) * (Real.sqrt (3 * x ^ 2 - 2 * x + 8)) - (-3 * x ^ 2 + 2 * x + 13))]
    have h10 : (x - 1) * (x + 1 / 3) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h10) with h11 h12 
    · -- x - 1 = 0, so x = 1 
      right 
      linarith 
    · -- x + 1/3 = 0, so x = -1/3 
      left 
      linarith 
  · -- Assume x = -1/3 or 1, prove the equation
    rintro (h_eq | h_eq) 
    · -- x = -1/3 
      rw [show x = -1 / 3 by linarith] 
      have h1 : Real.sqrt (3 * (-1 / 3) ^ 2 - 2 * (-1 / 3) + 15) = 4 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h2 : Real.sqrt (3 * (-1 / 3) ^ 2 - 2 * (-1 / 3) + 8) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h1, h2] 
      all_goals norm_num 
    · -- x = 1 
      rw [show x = 1 by linarith] 
      have h1 : Real.sqrt (3 * (1 : ℝ) ^ 2 - 2 * (1 : ℝ) + 15) = 4 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h2 : Real.sqrt (3 * (1 : ℝ) ^ 2 - 2 * (1 : ℝ) + 8) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h1, h2] 
      all_goals norm_num