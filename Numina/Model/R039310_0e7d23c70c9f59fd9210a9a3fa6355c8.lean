import Mathlib

theorem algebra_10283 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + 1 / y = 4) (h2 : y + 1 / z = 1) (h3 : z + 1 / x = 7 / 3) :
    x * y * z = 1 := by
  have hxxyz : 0 < x * y * z := by positivity
  have heq3 : x * y * z + 1 / (x * y * z) = 2 := by
    have eq1' : (x + 1 / y) * (y + 1 / z) * (z + 1 / x) = x * y * z + (x + 1 / y) + (y + 1 / z) + (z + 1 / x) + 1 / (x * y * z) := by
      field_simp
      ring
    have eq2' : (x + 1 / y) * (y + 1 / z) * (z + 1 / x) = 4 * 1 * (7 / 3) := by
      rw [h1, h2, h3]
    have eq3' : x * y * z + (x + 1 / y) + (y + 1 / z) + (z + 1 / x) + 1 / (x * y * z) = 4 * 1 * (7 / 3) := by
      linarith [eq1', eq2']
    have ht1 : x + 1 / y + (y + 1 / z) + (z + 1 / x) = 4 + 1 + (7 / 3) := by
      linarith [h1, h2, h3]
    field_simp [show x ≠ 0 by linarith, show y ≠ 0 by linarith, show z ≠ 0 by linarith] at eq3' ht1 ⊢
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  -- Now from `u + 1/u = 2`, proving `u = 1`.
  have hxxy1 : (x * y * z) ^ 2 + 1 = 2 * (x * y * z) := by
    have eq8 : (x * y * z) + 1 / (x * y * z) = 2 := heq3
    have eq9 : x * y * z ≠ 0 := by
      positivity 
    field_simp at eq8
    nlinarith
  have hxxy2 : (x * y * z - 1) ^ 2 = 0 := by
    nlinarith
  have hx1 : x * y * z - 1 = 0 := by
    apply pow_eq_zero 
    exact hxxy2
  have hx11 : x * y * z = 1 := by
    linarith
  exact hx11