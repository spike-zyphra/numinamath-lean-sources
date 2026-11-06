import Mathlib

theorem algebra_183835 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (x + 10) * y = 1000) (h2 : (x - 4) * y = 650) :
    x * y = 750 := by
  have eq1 : 14 * y = 350 := by
    nlinarith
  have hy_val : y = 25 := by
    linarith
  have eq2 : x = 30 := by
    rw [hy_val] at h1
    nlinarith
  rw [eq2, hy_val]
  norm_num