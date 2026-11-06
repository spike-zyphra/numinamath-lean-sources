import Mathlib

theorem algebra_3228 {x y z : ℝ} (h : (x + 3) / 4 = (2 * y - 1) / 3 ∧ (2 * y - 1) / 3 = (3 * z + 2) / 7 ∧ x + y + z = 36) :
    x = 17 := by
  rcases h with ⟨h1, h2, h3⟩
  linarith