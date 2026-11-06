import Mathlib

theorem algebra_504 {x y : ℝ} (h₁ : 2 * x + 3 * y = 15) (h₂ : 6 * x + 13 * y = 41) : x + 2 * y = 7 := by 
  have eq1 : 6 * x + 9 * y = 45 := by
    linarith [h₁]
  have hy : y = -1 := by
    linarith [eq1, h₂]
  have hx : x = 9 := by
    linarith [h₁, hy]
  linarith [hx, hy]