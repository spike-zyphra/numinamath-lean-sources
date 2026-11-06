import Mathlib

theorem algebra_254161 (a b c : ℝ) (h₀ : a + b + c = 2) (h₁ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 4 / 3 := by
  have h2 : b + c = 2 - a := by linarith
  have h3 : a * (b + c) + b * c = 1 := by
    nlinarith
  have h4 : b * c = (a - 1) ^ 2 := by
    rw [h2] at h3
    nlinarith
  have h5 : (b - c) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h6 : (b - c) ^ 2 = (b + c) ^ 2 - 4 * (b * c) := by
    ring
  rw [h6] at h5
  rw [h2, h4] at h5
  have h7 : 4 * a - 3 * a ^ 2 ≥ 0 := by
    nlinarith
  constructor
  · -- Prove that 0 ≤ a
    nlinarith
  · -- Prove that a ≤ 4 / 3
    nlinarith