import Mathlib

open Real

theorem inequalities_276438 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1 / x + 1 / y + 1 / z) :
    sqrt ((x * y + 1) / 2) + sqrt ((y * z + 1) / 2) +
    sqrt ((z * x + 1) / 2) ≤ x + y + z := by
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : (x + y + z) * (x * y * z) = x * y + y * z + z * x := by
    have h3 : 1 / x + 1 / y + 1 / z = (x * y + y * z + z * x) / (x * y * z) := by
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      <;> ring
    have h2' : x + y + z = (x * y + y * z + z * x) / (x * y * z) := by linarith [h, h3]
    have h4 : (x + y + z) * (x * y * z) = x * y + y * z + z * x := by
      have : (x + y + z) * (x * y * z) = (x * y + y * z + z * x) := by
        field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm] at h2' ⊢
        nlinarith [h2', mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      linarith
    linarith
  have h5 : sqrt ((x * y + 1) / 2) + sqrt ((y * z + 1) / 2) + sqrt ((z * x + 1) / 2) ≤ x + y + z := by
    nlinarith [sq_nonneg (sqrt ((x * y + 1) / 2) - x), sq_nonneg (sqrt ((y * z + 1) / 2) - y), sq_nonneg (sqrt ((z * x + 1) / 2) - z), Real.sqrt_nonneg ((x * y + 1) / 2), Real.sqrt_nonneg ((y * z + 1) / 2), Real.sqrt_nonneg ((z * x + 1) / 2), Real.sq_sqrt (show 0 ≤ (x * y + 1) / 2 by positivity), Real.sq_sqrt (show 0 ≤ (y * z + 1) / 2 by positivity), Real.sq_sqrt (show 0 ≤ (z * x + 1) / 2 by positivity), sq_nonneg (x * y * z - 1), h, h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, Real.sqrt_nonneg ((x * y + 1) / 2), Real.sqrt_nonneg ((y * z + 1) / 2), Real.sqrt_nonneg ((z * x + 1) / 2)]
  exact h5