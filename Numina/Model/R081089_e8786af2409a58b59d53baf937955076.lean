import Mathlib

theorem algebra_321295 {x y : ℝ} (h₀ : 1995 * x + 1997 * y = 5989) (h₁ : 1997 * x + 1995 * y = 5987) :
    x ^ 3 * y ^ 2 / (x ^ 2 + y ^ 2) = 4 / 5 := by
  have h2 : x + y = 3 := by
    linarith
  have h3 : -x + y = 1 := by
    linarith
  have hy : y = 2 := by 
    linarith [h2, h3]
  have hx : x = 1 := by 
    linarith [h2, hy]
  have eq1 : x ^ 3 * y ^ 2 = 4 := by
    rw [hx, hy]
    norm_num
  have eq2 : x ^ 2 + y ^ 2 = 5 := by
    rw [hx, hy]
    norm_num
  rw [eq1, eq2]