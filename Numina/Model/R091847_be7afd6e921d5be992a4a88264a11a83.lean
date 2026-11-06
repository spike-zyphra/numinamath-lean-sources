import Mathlib

open Real

theorem inequalities_233343 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    x^2 + y^2 + z^2 + 2 * sqrt (3 * x * y * z) ≤ 1 := by
  have h1 : x ^ 2 + y ^ 2 + z ^ 2 = 1 - 2 * (x * y + y * z + z * x) := by
    nlinarith [h]
  have h2 : 3 * x * y * z ≤ (x * y + y * z + z * x) ^ 2 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
  have h3 : sqrt (3 * x * y * z) ≤ x * y + y * z + z * x := by
    have h4 : (3 * x * y * z) ≤ (x * y + y * z + z * x) ^ 2 := h2
    have h5 : sqrt (3 * x * y * z) ≤ sqrt ((x * y + y * z + z * x) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    have h6 : sqrt ((x * y + y * z + z * x) ^ 2) = (x * y + y * z + z * x) := by
      rw [Real.sqrt_sq (by nlinarith)]
    linarith [h5, h6]
  rw [h1]
  nlinarith [h3, Real.sqrt_nonneg (3 * x * y * z)]