import Mathlib

theorem algebra_60569 {x y : ℚ} (hxy : x = y + 12) (hsum : x^2 + y^2 = 169 / 2)
    (hdiff : x^4 - y^4 = 5070) : x + y = 5 := by

  have eq1 : x = y + 12 := hxy

  have eq2 : (y + 12) ^ 2 + y ^ 2 = 169 / 2 := by
    rw [eq1] at hsum
    linarith

  have eq3 : 4 * y ^ 2 + 48 * y + 119 = 0 := by
    nlinarith

  have hy1 : (y + 7 / 2) * (y + 17 / 2) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp hy1) with h1 h2

  · -- Case y + 7/2 = 0
    have eq4 : y = -7 / 2 := by
      linarith
    have eq5 : x = 17 / 2 := by
      rw [eq1]
      linarith [eq4]
    have eq6 : x + y = 5 := by
      rw [eq5, eq4]
      norm_num
    linarith

  · -- Case y + 17/2 = 0
    have eq7 : y = -17 / 2 := by
      linarith
    have eq8 : x = 7 / 2 := by
      rw [eq1]
      linarith [eq7]
    rw [eq8, eq7] at hdiff
    norm_num at hdiff