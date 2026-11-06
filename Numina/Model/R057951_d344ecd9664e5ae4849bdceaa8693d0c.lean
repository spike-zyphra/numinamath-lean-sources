import Mathlib

theorem algebra_302327 {m : ℝ} (h : ∃ x, x^2 - 4 * x + m = 0 ∧ x = 2) : m = 4 := by
  rcases h with ⟨x, hx1, hx2⟩
  rw [hx2] at hx1
  nlinarith