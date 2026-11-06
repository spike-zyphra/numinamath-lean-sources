import Mathlib

theorem algebra_181935 (a b c : ℝ) (h₀ : a^2 - b * c - 8 * a + 7 = 0) (h₁ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by

  have h2 : b * c = a ^ 2 - 8 * a + 7 := by
    linarith [h₀]

  have h5 : 3 * (b * c) ≤ b^2 + c^2 + b * c := by
    nlinarith [sq_nonneg (b - c)]

  have h6 : 3 * (b * c) ≤ 6 * a - 6 := by
    nlinarith [h₁, sq_nonneg (b - c)]

  rw [h2] at h6

  constructor
  · -- Prove 1 ≤ a
    nlinarith
  · -- Prove a ≤ 9
    nlinarith