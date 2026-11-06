import Mathlib

theorem algebra_171665 (x : ℝ) :
    2 * x + 1 + x * Real.sqrt (x ^ 2 + 1) +
    (x + 1) * Real.sqrt (x ^ 2 + 2 * x + 2) = 0 ↔ x = -1 / 2 := by 
  constructor
  · -- Forward: equation implies x = -1/2
    intro h
    by_cases h4 : x ≥ -1 / 2
    · -- Case x = -1/2
      by_cases h5 : x > -1 / 2
      · -- Assume x > -1/2, derive contradiction
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 + 2 * x + 2),
          Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by nlinarith), 
          Real.sq_sqrt (show 0 ≤ x ^ 2 + 2 * x + 2 by nlinarith), 
          sq_nonneg (x + 1 / 2), sq_nonneg (x), sq_nonneg (x + 1), 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1)) (Real.sqrt_nonneg (x ^ 2 + 2 * x + 2))]
      · -- Assume x = -1/2
        have h6 : x = -1 / 2 := by linarith
        exact h6
    · -- Assume x < -1/2
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 + 2 * x + 2),
        Real.sq_sqrt (show 0 ≤ x ^ 2 + 1 by nlinarith), 
        Real.sq_sqrt (show 0 ≤ x ^ 2 + 2 * x + 2 by nlinarith), 
        sq_nonneg (x + 1 / 2), sq_nonneg (x), sq_nonneg (x + 1), 
        mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1)) (Real.sqrt_nonneg (x ^ 2 + 2 * x + 2))]
  · -- Backward: x = -1/2 implies equation
    intro h
    rw [h]
    have h10 : Real.sqrt ((-1 / 2 : ℝ) ^ 2 + 1) = Real.sqrt (5 / 4 : ℝ) := by norm_num
    have h11 : Real.sqrt ((-1 / 2 : ℝ) ^ 2 + 2 * (-1 / 2 : ℝ) + 2) = Real.sqrt (5 / 4 : ℝ) := by norm_num
    have h45 : Real.sqrt (5 / 4 : ℝ) = Real.sqrt (5 : ℝ) / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf 
      <;> norm_num
    rw [h10, h11, h45]
    nlinarith [Real.sqrt_nonneg (5 / 4 : ℝ), Real.sqrt_nonneg (5 : ℝ)]