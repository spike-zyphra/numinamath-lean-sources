import Mathlib

theorem algebra_223443 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 120 * x = (1 - 40 / 100) * y) (h2 : 185 * x = y - 1350) :
    y = 18000 := by
  have eq1 : y = 200 * x := by
    have eq2 : (1 - 40 / 100 : ℝ) * y = 120 * x := by
      linarith 
    norm_num at eq2
    linarith
  have eq2 : y = 1350 + 185 * x := by
    linarith
  have eq3 : 200 * x = 1350 + 185 * x := by
    have eq4 : y = 200 * x := eq1
    rw [eq4] at eq2
    linarith
  have hx_eq : x = 90 := by
    linarith
  have hy_eq : y = 18000 := by
    rw [hx_eq] at eq1
    linarith
  linarith