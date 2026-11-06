import Mathlib

theorem algebra_13796 {x y : ℝ} (h1 : 2 * x + y = 4) (h2 : x + 2 * y = 5) :
    5 * x ^ 2 + 8 * x * y + 5 * y ^ 2 = 41 := by
  have eq1 : x = 1 := by
    have eq3 : 4 * x + 2 * y = 8 := by
      linarith [h1]
    have eq4 : 3 * x = 3 := by
      linarith [eq3, h2]
    linarith
  have eq2 : y = 2 := by
    rw [eq1] at h1
    linarith
  rw [eq1, eq2]
  norm_num