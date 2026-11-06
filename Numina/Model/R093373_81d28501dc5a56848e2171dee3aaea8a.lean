import Mathlib

theorem algebra_253155 (a b c : ℝ) (h₁ : b + c = 6 - 4 * a + 3 * a ^ 2) (h₂ : c - b = 4 - 4 * a + a ^ 2) :
    a < b ∧ b ≤ c := by
  have h3 : c = 5 - 4 * a + 2 * a ^ 2 := by
    nlinarith [h₁, h₂]
  have h4 : b = 1 + a ^ 2 := by
    nlinarith [h₁, h₂]
  have h5 : a < b := by
    rw [show b = 1 + a ^ 2 by linarith [h4]]
    nlinarith [sq_nonneg (a - 1 / 2)]
  have h6 : b ≤ c := by
    rw [show b = 1 + a ^ 2 by linarith [h4], show c = 5 - 4 * a + 2 * a ^ 2 by linarith [h3]]
    nlinarith [sq_nonneg (a - 2)]
  exact ⟨h5, h6⟩