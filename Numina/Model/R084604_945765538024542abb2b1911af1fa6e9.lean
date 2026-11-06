import Mathlib

open Real

theorem inequalities_99928 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x y : ℝ) (hx : x = sqrt (a^2 + b^2)) (hy : y = sqrt (c^2 + d^2)) :
    x * y ≥ a * c + b * d := by
  rw [hx, hy]
  have h1 : sqrt (a ^ 2 + b ^ 2) * sqrt (c ^ 2 + d ^ 2) ≥ a * c + b * d := by
    have h2 : (sqrt (a ^ 2 + b ^ 2) * sqrt (c ^ 2 + d ^ 2)) ^ 2 ≥ (a * c + b * d) ^ 2 := by
      have h3 : (sqrt (a ^ 2 + b ^ 2) * sqrt (c ^ 2 + d ^ 2)) ^ 2 = (sqrt (a ^ 2 + b ^ 2)) ^ 2 * (sqrt (c ^ 2 + d ^ 2)) ^ 2 := by
        ring
      have h4 : (sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      have h5 : (sqrt (c ^ 2 + d ^ 2)) ^ 2 = c ^ 2 + d ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      rw [h3, h4, h5]
      nlinarith [sq_nonneg (a * d - b * c)]
    have h5 : sqrt (a ^ 2 + b ^ 2) * sqrt (c ^ 2 + d ^ 2) ≥ 0 := by
      apply mul_nonneg
      · -- Show sqrt (a^2 + b^2) ≥ 0
        apply Real.sqrt_nonneg
      · -- Show sqrt (c^2 + d^2) ≥ 0
        apply Real.sqrt_nonneg
    have h6 : a * c + b * d ≥ 0 := by
      nlinarith
    nlinarith [h2, Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg (c ^ 2 + d ^ 2), h5, h6]
  linarith [h1]