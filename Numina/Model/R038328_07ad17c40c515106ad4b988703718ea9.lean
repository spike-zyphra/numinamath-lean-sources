import Mathlib

theorem algebra_319211 {a b c x y : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hA : x = (a + b) / c + (b + c) / a + (c + a) / b) (hA' : y = (a + b) / c * (b + c) / a * (c + a) / b)
    (hxy : x = 2 * y) : x + y = -6 := by
  have eq1 : y = x + 2 := by
    rw [hA']
    have eq2 : (a + b) / c * (b + c) / a * (c + a) / b = x + 2 := by
      rw [hA]
      field_simp [ha, hb, hc]
      ring
    linarith [eq2]
  have eq2 : x = -4 := by
    rw [eq1] at hxy 
    linarith
  have eq3 : y = -2 := by
    linarith [eq1, eq2]
  linarith [eq2, eq3]