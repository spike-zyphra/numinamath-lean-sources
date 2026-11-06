import Mathlib

theorem algebra_10662 (x y : ℝ) (h : 3 * x + 5 * y = 20) (hy : y = 0) :
    (x, y) = (20 / 3, 0) := by 
  have eq1 : 3 * x + 5 * (0 : ℝ) = 20 := by 
    rw [hy] at h 
    linarith 
  have hx : x = 20 / 3 := by 
    linarith [eq1] 
  simp [Prod.ext_iff, hx, hy]