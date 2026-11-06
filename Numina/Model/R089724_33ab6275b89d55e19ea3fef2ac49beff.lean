import Mathlib

theorem algebra_163162 (x : Fin 7 → ℝ)
    (h₀ : (x 3 + x 4 + x 5 + x 6) / 4 = (x 0 + x 1 + x 2) / 3 + 4)
    (h₁ : (x 4 + x 5 + x 6) / 3 = (x 0 + x 1 + x 2 + x 3) / 4 + 3) :
    (x 4 + x 5 + x 6) - (x 0 + x 1 + x 2) = 12 := by
  have eq1 : 3 * (x 3 + x 4 + x 5 + x 6) = 4 * (x 0 + x 1 + x 2) + 48 := by
    linarith [h₀]
  have eq2 : 4 * (x 4 + x 5 + x 6) = 3 * (x 0 + x 1 + x 2 + x 3) + 36 := by
    linarith [h₁]
  linarith [eq1, eq2]