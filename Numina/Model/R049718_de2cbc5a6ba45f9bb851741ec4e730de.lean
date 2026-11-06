import Mathlib

theorem algebra_20829 {x y : ℝ} (h₀ : x + y = 3 - x + 3 - y) (h₁ : x - y = x - 2 + y - 2) :
    (x, y) = (1, 2) := by
  have eq1 : x + y = 3 := by
    linarith
  have eq2 : y = 2 := by
    linarith
  have hx : x = 1 := by
    linarith [eq1, eq2]
  simp [hx, eq2]