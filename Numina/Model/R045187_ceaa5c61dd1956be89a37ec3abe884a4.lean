import Mathlib

open Real

theorem inequalities_46000 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1 / x + 1 / y + 1 / z) :
    x + y + z ≥ sqrt ((x * y + 1) / 2) + sqrt ((y * z + 1) / 2) +
    sqrt ((z * x + 1) / 2) := by 
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : x * y * z * (x + y + z) = y * z + x * z + x * y := by
    have eq1 : 1 / x + 1 / y + 1 / z = (y * z + x * z + x * y) / (x * y * z) := by
      field_simp
      <;> ring
      <;> field_simp
    rw [eq1] at h
    have eq2 : x * y * z > 0 := h1
    have eq3 : x * y * z * (x + y + z) = y * z + x * z + x * y := by
      field_simp at h ⊢
      nlinarith [h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith
  have h3 : (sqrt ((x * y + 1) / 2) + sqrt ((y * z + 1) / 2) + sqrt ((z * x + 1) / 2)) ^ 2 ≤ (x + y + z)^2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      Real.sqrt_nonneg ((x * y + 1) / 2), Real.sqrt_nonneg ((y * z + 1) / 2), Real.sqrt_nonneg ((z * x + 1) / 2),
      sq_nonneg (sqrt ((x * y + 1) / 2) - sqrt ((y * z + 1) / 2)), sq_nonneg (sqrt ((y * z + 1) / 2) - sqrt ((z * x + 1) / 2)), sq_nonneg (sqrt ((z * x + 1) / 2) - sqrt ((x * y + 1) / 2)),
      Real.sq_sqrt (show (0 : ℝ) ≤ (x * y + 1) / 2 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (y * z + 1) / 2 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (z * x + 1) / 2 by nlinarith),
      h2, sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
  have h4 : sqrt ((x * y + 1) / 2) + sqrt ((y * z + 1) / 2) + sqrt ((z * x + 1) / 2) ≤ x + y + z := by
    nlinarith [h3, sq_nonneg (x + y + z - (sqrt ((x * y + 1) / 2) + sqrt ((y * z + 1) / 2) + sqrt ((z * x + 1) / 2))), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, Real.sqrt_nonneg ((x * y + 1) / 2), Real.sqrt_nonneg ((y * z + 1) / 2), Real.sqrt_nonneg ((z * x + 1) / 2)]
  linarith [h4]