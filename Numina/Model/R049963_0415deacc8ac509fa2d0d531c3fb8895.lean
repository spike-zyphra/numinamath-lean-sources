import Mathlib

theorem algebra_287359 (a b c : ℝ)
    (h₁ : a^2 - b * c - 8 * a + 7 = 0)
    (h₂ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by
  have h3 : b * c = a^2 - 8 * a + 7 := by 
    linarith
  have h4 : b^2 + c^2 = -a^2 + 14 * a - 13 := by 
    have h5 : b^2 + c^2 + b * c - 6 * a + 6 = 0 := by linarith
    rw [h3] at h5
    nlinarith
  have h6 : b^2 + c^2 ≥ 2 * (b * c) := by
    nlinarith [sq_nonneg (b - c)]
  rw [h4, h3] at h6
  have h7 : -a^2 + 14 * a - 13 ≥ 2 * (a^2 - 8 * a + 7) := by linarith
  have h8 : a^2 - 10 * a + 9 ≤ 0 := by 
    nlinarith
  constructor
  · -- Prove 1 ≤ a
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]
  · -- Prove a ≤ 9
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]