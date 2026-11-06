import Mathlib

theorem inequalities_29447 (a b c : ℝ) (h₀ : a + b + c = 1) (h₁ : a^2 + b^2 + c^2 = 1) :
    -1 / 4 ≤ a * b ∧ a * b ≤ 4 / 9 := by
  have h2 : a * b + a * c + b * c = 0 := by
    have h2 : a * b + a * c + b * c = 0 := by
      have h2 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by ring
      rw [h₀, h₁] at h2
      linarith
    assumption

  constructor
  · -- Prove that -1/4 ≤ a * b.
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a + b - 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (a - b), sq_nonneg (a + b - c)]
  · -- Prove that a * b ≤ 4/9.
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a + b - 2 / 3), sq_nonneg (c + 1 / 3), sq_nonneg (a - b), sq_nonneg (a + b - c)]