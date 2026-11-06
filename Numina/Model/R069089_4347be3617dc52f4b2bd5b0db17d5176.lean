import Mathlib

theorem algebra_599384 (a b c : ℝ) (h1 : a^2 - b * c - 8 * a + 7 = 0) (h2 : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by

  have h3 : b * c = a ^ 2 - 8 * a + 7 := by linarith

  have h4 : b^2 + c^2 + b * c = 6 * a - 6 := by linarith

  have h5 : b ^ 2 + c ^ 2 ≥ 2 * (b * c) := by
    linarith [sq_nonneg (b - c)]

  have h6 : (b^2 + c^2) + (b * c) ≥ 3 * (b * c) := by
    linarith [h5]

  have h7 : 6 * a - 6 ≥ 3 * (b * c) := by linarith [h4, h6]

  rw [h3] at h7

  constructor
  · -- Prove that 1 ≤ a
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]
  · -- Prove that a ≤ 9
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]