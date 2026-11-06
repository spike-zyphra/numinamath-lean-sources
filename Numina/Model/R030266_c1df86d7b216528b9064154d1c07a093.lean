import Mathlib

open Real

theorem algebra_122899 (x : ℝ) (hx : 0 ≤ x) :
    sqrt (x + sqrt (4 * x + sqrt (16 * x + 3))) - sqrt x = 1 ↔ x = 1 / 16 := by
  constructor
  · -- Assume sqrt (x + sqrt (4 * x + sqrt (16 * x + 3))) - sqrt x = 1, prove x = 1 / 16
    intro h
    have h1 : sqrt (x + sqrt (4 * x + sqrt (16 * x + 3))) = sqrt x + 1 := by
      linarith
    have h2 : x + sqrt (4 * x + sqrt (16 * x + 3)) = (sqrt x + 1) ^ 2 := by
      calc
        x + sqrt (4 * x + sqrt (16 * x + 3)) = (sqrt (x + sqrt (4 * x + sqrt (16 * x + 3)))) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (sqrt x + 1) ^ 2 := by
          rw [h1]
    have h3 : sqrt (4 * x + sqrt (16 * x + 3)) = 2 * sqrt x + 1 := by
      nlinarith [Real.sqrt_nonneg (x + sqrt (4 * x + sqrt (16 * x + 3))), Real.sqrt_nonneg x, 
        Real.sq_sqrt (show x ≥ 0 by linarith)]
    have h4 : 4 * x + sqrt (16 * x + 3) = (2 * sqrt x + 1) ^ 2 := by
      calc
        4 * x + sqrt (16 * x + 3) = (sqrt (4 * x + sqrt (16 * x + 3))) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (2 * sqrt x + 1) ^ 2 := by 
          rw [h3]
    have h5 : sqrt (16 * x + 3) = 4 * sqrt x + 1 := by
      nlinarith [Real.sqrt_nonneg (4 * x + sqrt (16 * x + 3)), Real.sqrt_nonneg x, 
        Real.sq_sqrt (show x ≥ 0 by linarith)]
    have h6 : 16 * x + 3 = (4 * sqrt x + 1) ^ 2 := by
      calc
        16 * x + 3 = (sqrt (16 * x + 3)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (4 * sqrt x + 1) ^ 2 := by
          rw [h5]
    have h7 : sqrt x = 1 / 4 := by 
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show x ≥ 0 by linarith)]
    have h8 : x = 1 / 16 := by 
      calc
        x = (sqrt x) ^ 2 := by 
          rw [Real.sq_sqrt]
          linarith
        _ = (1 / 4) ^ 2 := by 
          rw [h7]
        _ = 1 / 16 := by 
          norm_num
    exact h8
  · -- Assume x = 1/16, prove sqrt (x + sqrt (4 * x + sqrt (16 * x + 3))) - sqrt x = 1
    intro h
    rw [h]
    have h1 : sqrt (1 / 16 : ℝ) = 1 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (16 * (1 / 16 : ℝ) + 3) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : sqrt (4 * (1 / 16 : ℝ) + sqrt (16 * (1 / 16 : ℝ) + 3)) = (3 / 2 : ℝ) := by
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : sqrt ((1 / 16 : ℝ) + sqrt (4 * (1 / 16 : ℝ) + sqrt (16 * (1 / 16 : ℝ) + 3))) = (5 / 4 : ℝ) := by
      rw [h3]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h4, h1]
    all_goals norm_num