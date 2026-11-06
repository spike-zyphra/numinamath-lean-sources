import Mathlib

theorem algebra_288295 {x1 x2 : ℝ} (hx1 : x1 = -3) (hx2 : x2 = 7) :
    (x1 + x2) / 2 = 2 := by 
  rw [hx1, hx2]
  norm_num