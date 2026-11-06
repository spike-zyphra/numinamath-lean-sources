import Mathlib

open Real Set

theorem algebra_204 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 2 * sqrt (x * y) + sqrt (x * z) = 1) :
    3 * y * z / x + 4 * z * x / y + 5 * x * y / z ≥ 4 := by
  have h1 : 0 < sqrt (x * y) := by
    apply Real.sqrt_pos.mpr
    positivity
  have h2 : 0 < sqrt (x * z) := by
    apply Real.sqrt_pos.mpr
    positivity
  have h3 : sqrt (x * y) ^ 2 = x * y := by
    exact Real.sq_sqrt (by positivity)
  have h4 : sqrt (x * z) ^ 2 = x * z := by
    exact Real.sq_sqrt (by positivity)
  have h5 : sqrt (x * y) ≥ 0 := Real.sqrt_nonneg (x * y)
  have h6 : sqrt (x * z) ≥ 0 := Real.sqrt_nonneg (x * z)
  have h7 : 3 * y * z / x + 4 * z * x / y + 5 * x * y / z ≥ 4 := by
    have h8 : 3 * y * z / x + 4 * z * x / y + 5 * x * y / z - 4 ≥ 0 := by
      have h9 : 3 * y * z / x + 4 * z * x / y + 5 * x * y / z - 4 =
          (3 * y^2 * z^2 + 4 * x^2 * z^2 + 5 * x^2 * y^2 - 4 * x * y * z) / (x * y * z) := by
        field_simp
        <;> ring_nf
        <;> field_simp
        <;> ring
      rw [h9]
      have h10 : 0 < x * y * z := by
        positivity
      have h11 : 3 * y^2 * z^2 + 4 * x^2 * z^2 + 5 * x^2 * y^2 - 4 * x * y * z ≥ 0 := by
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), sq_nonneg (sqrt (x * y) - sqrt (x * z) / 2), sq_nonneg (sqrt (x * y) - 1/3), sq_nonneg (sqrt (x * z) - 1/3),
            h, h3, h4, mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (x * z)), Real.sqrt_nonneg (x * y), Real.sqrt_nonneg (x * z), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith