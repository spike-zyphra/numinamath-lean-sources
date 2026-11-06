import Mathlib

theorem algebra_16261 {k : ℝ} (h : ∃ x, 5 * x + 3 = -2 * x - 25 ∧ -2 * x - 25 = 3 * x + k) :
    k = -5 := by
  rcases h with ⟨x, h1, h2⟩
  have hx : x = -4 := by
    linarith
  rw [hx] at h2
  linarith