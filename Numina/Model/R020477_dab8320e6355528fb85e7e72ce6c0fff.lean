import Mathlib

theorem algebra_252147 (x : ℝ) (hx : 1 ≤ x) : Real.sqrt (2 * x + 5) + Real.sqrt (x - 1) = 8 ↔ x = 10 := by
  constructor
  · -- Forward: if the equation holds, then x = 10
    intro h
    have h1 : 0 ≤ Real.sqrt (2 * x + 5) := Real.sqrt_nonneg (2 * x + 5)
    have h2 : 0 ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg (x - 1)
    have h3 : Real.sqrt (2 * x + 5) = 8 - Real.sqrt (x - 1) := by linarith
    have h4 : Real.sqrt (2 * x + 5) ^ 2 = (8 - Real.sqrt (x - 1)) ^ 2 := by
      rw [h3]
    have h5 : Real.sqrt (2 * x + 5) ^ 2 = 2 * x + 5 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h6 : Real.sqrt (x - 1) ^ 2 = x - 1 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h7 : (8 - Real.sqrt (x - 1)) ^ 2 = 2 * x + 5 := by
      nlinarith [h4, h5]
    nlinarith [Real.sqrt_nonneg (2 * x + 5), Real.sqrt_nonneg (x - 1),
      sq_nonneg (Real.sqrt (2 * x + 5) - 5), sq_nonneg (Real.sqrt (x - 1) - 3),
      Real.sqrt_nonneg (2 * x + 5), Real.sqrt_nonneg (x - 1)]
  · -- Backward: if x = 10, then the equation
    intro h
    rw [h]
    have h1 : Real.sqrt (2 * (10 : ℝ) + 5) = 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (10 - 1 : ℝ) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num