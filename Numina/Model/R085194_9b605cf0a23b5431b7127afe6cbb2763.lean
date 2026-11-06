import Mathlib

theorem algebra_597558 (a b c : ℝ)
    (h₀ : a^2 - b * c - 8 * a + 7 = 0)
    (h₁ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by
  have h2 : b * c = a^2 - 8 * a + 7 := by nlinarith
  have h3 : b^2 + c^2 = -a^2 + 14 * a - 13 := by
    nlinarith [h₀, h₁]
  have h4 : b^2 + c^2 ≥ 2 * (b * c) := by
    nlinarith [sq_nonneg (b - c)]
  rw [h3, h2] at h4

  have h5 : a ^ 2 - 10 * a + 9 ≤ 0 := by
    nlinarith [sq_nonneg (a), sq_nonneg (a - 9), sq_nonneg (a - 1)]

  constructor
  · -- 1 ≤ a
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]
  · -- a ≤ 9
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]