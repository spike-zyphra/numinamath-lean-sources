import Mathlib

theorem algebra_3274 {x : ℝ} (h : 3 * x ^ 2 + 7 * x + 5 = 2 + x) : x ^ 3 + x ^ 2 - x + 6 = 7 := by
  have eq1 : 3 * x ^ 2 + 6 * x + 3 = 0 := by
    linarith
  have eq2 : (x + 1) ^ 2 = 0 := by
    nlinarith
  have hx : x + 1 = 0 := by
    apply pow_eq_zero 
    exact eq2
  have hx2 : x = -1 := by linarith
  rw [hx2]
  norm_num