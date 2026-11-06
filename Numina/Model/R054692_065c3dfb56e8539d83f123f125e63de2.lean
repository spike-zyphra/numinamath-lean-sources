import Mathlib

theorem algebra_316681 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : (1 + 50 / 100) * y = x) (h' : (40 / 100) * x + (60 / 100) * y = 50 / 100 * (x + y)) :
    (40 / 100) * x + (60 / 100) * y = 48 / 100 * (x + y) := by
  have hx_eq : x = (1 + 50 / 100) * y := by 
    linarith 
  rw [hx_eq] at h' 
  linarith