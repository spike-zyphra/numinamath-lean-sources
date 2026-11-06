import Mathlib

theorem algebra_3690 {x y : ℝ} (h : 3 * x + 2 * y - 1 / 7 = 0 ∧ 8 * x + 5 * y - 5 / 4 = 0) :
    11 * x + 6 * y = 4 := by
  rcases h with ⟨h₁, h₂⟩
  linarith