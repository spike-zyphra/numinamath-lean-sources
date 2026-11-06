import Mathlib

theorem algebra_99627 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : y = 2 * x) (h' : x * 3 = y * 2) :
    (x + 2 * y) / x = 7 := by 
  rw [h] at h' 
  have h4 : x = 0 := by linarith 
  linarith -- Contradiction with hx : x > 0