import Mathlib

open Real Set

theorem inequalities_311883 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    sqrt 3 ≤ (sqrt (x^2 + y^2 + x * y) + sqrt (y^2 + z^2 + y * z) +
      sqrt (z^2 + x^2 + z * x)) / (x + y + z) := by
  have h1 : 0 < x + y + z := by
    linarith
  have h2 : sqrt (x^2 + y^2 + x * y) ≥ Real.sqrt 3 / 2 * (x + y) := by
    have h3 : x^2 + y^2 + x * y ≥ (Real.sqrt 3 / 2 * (x + y)) ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h4 : sqrt (x^2 + y^2 + x * y) ≥ sqrt ((Real.sqrt 3 / 2 * (x + y)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h5 : sqrt ((Real.sqrt 3 / 2 * (x + y)) ^ 2) = Real.sqrt 3 / 2 * (x + y) := by
      rw [Real.sqrt_sq]
      positivity
    rw [h5] at h4
    linarith
  have h3 : sqrt (y^2 + z^2 + y * z) ≥ Real.sqrt 3 / 2 * (y + z) := by
    have h4 : y^2 + z^2 + y * z ≥ (Real.sqrt 3 / 2 * (y + z)) ^ 2 := by
      nlinarith [sq_nonneg (y - z), sq_nonneg (y + z), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h5 : sqrt (y^2 + z^2 + y * z) ≥ sqrt ((Real.sqrt 3 / 2 * (y + z)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h6 : sqrt ((Real.sqrt 3 / 2 * (y + z)) ^ 2) = Real.sqrt 3 / 2 * (y + z) := by
      rw [Real.sqrt_sq]
      positivity
    rw [h6] at h5
    linarith
  have h4 : sqrt (z^2 + x^2 + z * x) ≥ Real.sqrt 3 / 2 * (z + x) := by
    have h5 : z^2 + x^2 + z * x ≥ (Real.sqrt 3 / 2 * (z + x)) ^ 2 := by
      nlinarith [sq_nonneg (z - x), sq_nonneg (z + x), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h6 : sqrt (z^2 + x^2 + z * x) ≥ sqrt ((Real.sqrt 3 / 2 * (z + x)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h7 : sqrt ((Real.sqrt 3 / 2 * (z + x)) ^ 2) = Real.sqrt 3 / 2 * (z + x) := by
      rw [Real.sqrt_sq]
      positivity
    rw [h7] at h6
    linarith
  have h7 : sqrt (x^2 + y^2 + x * y) + sqrt (y^2 + z^2 + y * z) + sqrt (z^2 + x^2 + z * x) ≥ Real.sqrt 3 * (x + y + z) := by
    nlinarith [h2, h3, h4]
  have h8 : (sqrt (x^2 + y^2 + x * y) + sqrt (y^2 + z^2 + y * z) + sqrt (z^2 + x^2 + z * x)) / (x + y + z) ≥ Real.sqrt 3 := by
    have h9 : 0 < x + y + z := h1
    have h10 : sqrt (x^2 + y^2 + x * y) + sqrt (y^2 + z^2 + y * z) + sqrt (z^2 + x^2 + z * x) ≥ Real.sqrt 3 * (x + y + z) := h7
    have h11 : (sqrt (x^2 + y^2 + x * y) + sqrt (y^2 + z^2 + y * z) + sqrt (z^2 + x^2 + z * x)) / (x + y + z) ≥ Real.sqrt 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    exact h11
  linarith [h8]