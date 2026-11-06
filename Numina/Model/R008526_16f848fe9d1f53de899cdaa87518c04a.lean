import Mathlib

theorem algebra_19701 {x : ℝ} (hx : x > 0) (h : 2 * (3 * x + 10 + x + 12) = 76) :
    (3 * x + 10) * (x + 12) = 352 := by
  have eq1 : 8 * x + 44 = 76 := by 
    linarith
  have eq2 : 8 * x = 32 := by
    linarith
  have hx_eq : x = 4 := by
    linarith
  rw [hx_eq]
  norm_num