import Mathlib

open Real

theorem inequalities_102653 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    sqrt (x^2 + x * y + y^2) ≥ sqrt 3 / 2 * (x + y) := by 
  have h1 : 0 < x + y := by linarith
  have h2 : sqrt (x^2 + x * y + y^2) ≥ sqrt 3 / 2 * (x + y) := by
    have h3 : sqrt (x^2 + x * y + y^2) ≥ 0 := by positivity
    have h4 : sqrt 3 / 2 * (x + y) ≥ 0 := by
      have h5 : sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
      nlinarith [h1]
    have h5 : (sqrt (x^2 + x * y + y^2)) ^ 2 ≥ (sqrt 3 / 2 * (x + y)) ^ 2 := by
      have h6 : (sqrt (x^2 + x * y + y^2)) ^ 2 = x^2 + x * y + y^2 := by
        rw [Real.sq_sqrt]
        positivity
      have h7 : (sqrt 3 / 2 * (x + y)) ^ 2 = (sqrt 3) ^ 2 / 4 * (x + y) ^ 2 := by
        ring_nf
      rw [h6, h7]
      have h8 : (sqrt 3) ^ 2 = 3 := by
        rw [Real.sq_sqrt]
        positivity
      rw [h8]
      nlinarith [sq_nonneg (x - y)]
    have h9 : sqrt (x^2 + x * y + y^2) ≥ sqrt 3 / 2 * (x + y) := by
      nlinarith [Real.sqrt_nonneg (x^2 + x * y + y^2), Real.sqrt_nonneg 3, sq_nonneg (x - y), mul_pos hx hy]
    linarith [h9]
  linarith [h2]