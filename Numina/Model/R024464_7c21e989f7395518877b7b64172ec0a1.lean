import Mathlib

theorem inequalities_190367 (a b c d : ℝ)
    (h₀ : a + b + c + d = 3)
    (h₁ : a^2 + 2*b^2 + 3*c^2 + 6*d^2 = 5) :
    1 ≤ a ∧ a ≤ 2 := by
  have h2 : b + c + d = 3 - a := by linarith
  have h3 : 2 * b^2 + 3 * c^2 + 6 * d^2 = 5 - a^2 := by 
    nlinarith
  have h4 : 2 * b^2 + 3 * c^2 + 6 * d^2 ≥ (b + c + d) ^ 2 := by 
    nlinarith [sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - b), 
      sq_nonneg (b - 3 * d), sq_nonneg (c - 2 * d), sq_nonneg (2 * b - 3 * c)]
  have h5 : 5 - a^2 ≥ (3 - a) ^ 2 := by
    have h8 : (b + c + d) = 3 - a := h2
    rw [h8] at h4 
    nlinarith [h3, h4]
  have h6 : a^2 - 3 * a + 2 ≤ 0 := by
    nlinarith 
  constructor
  · -- Show 1 ≤ a
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2)]
  · -- Show a ≤ 2
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2)]