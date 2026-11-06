import Mathlib

theorem algebra_11755 {b : ℝ} (h : ∃ x y, x + y = b ∧ (x - 1) ^ 2 + (y - 3) ^ 2 = (x - 5) ^ 2 + (y - 7) ^ 2) :
    b = 8 := by
  rcases h with ⟨x, y, h1, h2⟩
  have h3 : x + y = 8 := by
    nlinarith
  linarith