import Mathlib

theorem algebra_234514 {x y : ℝ} (hy : y > 0) (hx : x > 0)
    (h₁ : x = y + y / 3) (h₂ : y + 8 = (5 / 4) * (x - 8)) :
    y + 8 = 35 := by 
  linarith