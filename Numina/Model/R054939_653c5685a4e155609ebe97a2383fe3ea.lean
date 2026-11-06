import Mathlib

theorem algebra_21310 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : 1^3 * x + 1^2 * y = 1.30) (h2 : 2^3 * x + 2^2 * y = 6.80) :
    3^3 * x + 3^2 * y = 18.90 := by
  norm_num at h1 h2 ⊢
  have eq1 : x + y = 1.3 := by
    linarith
  have eq2 : 8 * x + 4 * y = 6.8 := by 
    linarith
  have hx_eq : x = 0.4 := by
    linarith [eq1, eq2]
  have hy_eq : y = 0.9 := by
    linarith [eq1, hx_eq]
  rw [hx_eq, hy_eq]
  all_goals norm_num