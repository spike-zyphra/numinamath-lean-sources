import Mathlib

theorem algebra_230004 (a : ℝ) (x y : ℝ)
    (h₀ : x + y = a) (h₁ : x ^ 2 + y ^ 2 = -a ^ 2 + 2) :
    x * y ≤ 1 / 3 ∧ x * y ≥ -1 := by
  have eq1 : x * y = a ^ 2 - 1 := by
    have h2 : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by
      ring
    rw [h₀, h₁] at h2
    linarith
  have eq2 : a ^ 2 ≤ 4 / 3 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - a), sq_nonneg (a), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y)]
  constructor
  · -- First part: proving the maximum value
    nlinarith [eq1, eq2]
  · -- Second part: proving the minimum value
    nlinarith [eq1, sq_nonneg a]