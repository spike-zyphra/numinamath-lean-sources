import Mathlib

theorem algebra_611052{x y z: ℝ}
  (eq1: (x+y)/(1+z) = (1-z+z^2)/(x^2-x*y+y^2))
  (eq1_den_ne_zero: 1+z ≠ 0 ∧ x^2-x*y+y^2 ≠ 0)
  (eq2: (x-y)/(3-z) = (9+3*z+z^2)/(x^2+x*y+y^2))
  (eq2_den_ne_zero: 3-z ≠ 0 ∧ x^2+x*y+y^2 ≠ 0):
  x = 14^(1/3:ℝ) := by

  have eq11 : (x + y) * (x^2 - x * y + y^2) = (1 + z) * (1 - z + z^2) := by 
    have h1 : 1 + z ≠ 0 := eq1_den_ne_zero.1 
    have h2 : x^2 - x * y + y^2 ≠ 0 := eq1_den_ne_zero.2 
    field_simp [h1, h2] at eq1 ⊢ 
    nlinarith 
  have eq22 : (x - y) * (x^2 + x * y + y^2) = (3 - z) * (9 + 3 * z + z^2) := by 
    have h1 : 3 - z ≠ 0 := eq2_den_ne_zero.1 
    have h2 : x^2 + x * y + y^2 ≠ 0 := eq2_den_ne_zero.2 
    field_simp [h1, h2] at eq2 ⊢ 
    nlinarith 
  have eq3 : (x + y) * (x^2 - x * y + y^2) + (x - y) * (x^2 + x * y + y^2) = 28 := by
    have eq11' : (x + y) * (x^2 - x * y + y^2) = (1 + z) * (1 - z + z^2) := eq11 
    have eq22' : (x - y) * (x^2 + x * y + y^2) = (3 - z) * (9 + 3 * z + z^2) := eq22
    nlinarith [sq_nonneg (z^2 - 1), sq_nonneg (z - 3), sq_nonneg (z + 1), sq_nonneg (z - 1)]
  have eq4 : (x + y) * (x^2 - x * y + y^2) + (x - y) * (x^2 + x * y + y^2) = 2 * x^3 := by 
    ring 
  have eq5 : 2 * x^3 = 28 := by 
    linarith [eq3, eq4] 
  have eq6 : x^3 = 14 := by 
    linarith [eq5] 
  have eq7 : x^3 = 14 := eq6 
  have eq8 : x = (14 : ℝ) ^ (1 / 3 : ℝ) := by 
    have eq9 : x ^ 3 = 14 := eq7 
    have eq10 : x = ((x ^ 3) ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num 
      all_goals nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
    rw [eq9] at eq10 
    rw [eq10] 
    all_goals nlinarith 
  linarith [eq8]