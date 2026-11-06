import Mathlib

theorem algebra_304959 (a b : ℝ) (h : a^3 - b^3 - 3 * a * b = 1) : a - b = 1 ∨ a - b = -2 := by 
  have h1 : (a - b - 1) * (3 * b ^ 2 + 3 * (a - b) * b + ((a - b) ^ 2 + (a - b) + 1)) = 0 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b - 1), sq_nonneg (a - b + 2), sq_nonneg (a - b), sq_nonneg (a - (b + 1)), sq_nonneg (a + b - (a - b)), sq_nonneg ((a - b) + 2)]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where a - b - 1 = 0
    left 
    linarith 
  · -- Case where the quadratic is zero 
    have h4 : 3 * b ^ 2 + 3 * (a - b) * b + ((a - b) ^ 2 + (a - b) + 1) = 0 := by 
      linarith [h3]
    have h5 : (a - b + 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b + 2), sq_nonneg (b + (a - b) / 3 + 2/3), sq_nonneg (a + b), sq_nonneg (a - b -1), sq_nonneg (a - (b + 1)), sq_nonneg (a + b - (a - b))]
    have h6 : a - b + 2 = 0 := by
      rw [sq_eq_zero_iff] at h5
      exact h5
    right 
    linarith