import Mathlib

open Real

theorem inequalities_215836 (x y : ℝ) 
    (hx : 0 < x) (hy : 0 < y) :
  (x^2 + x * y + y^2) / 3 ≤ (x + y) / 2 * sqrt ((x^2 + y^2) / 2) := by

  have h1 : 0 < x * y := mul_pos hx hy

  have h2 : 0 < x ^ 2 + x * y + y ^ 2 := by
    have h3 : 0 < x ^ 2 := sq_pos_of_pos hx
    have h4 : 0 < y ^ 2 := sq_pos_of_pos hy
    linarith

  have h3 : 0 < (x + y) / 2 := by
    linarith

  have h4 : 0 < (x ^ 2 + y ^ 2) / 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]

  have h5 : sqrt ((x ^ 2 + y ^ 2) / 2) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith

  have h6 : (x + y) / 2 * sqrt ((x ^ 2 + y ^ 2) / 2) > 0 := by
    apply mul_pos
    all_goals linarith

  have h7 : ((x ^ 2 + x * y + y ^ 2) / 3) ^ 2 ≤ ((x + y) / 2) ^ 2 * ((x ^ 2 + y ^ 2) / 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2),
      sq_nonneg (x * (x - y)), sq_nonneg (y * (y - x)), mul_pos hx hy,
      mul_pos hx h3, mul_pos hy h3, mul_pos hx h4, mul_pos hy h4, mul_pos hx (show 0 < x ^ 2 by positivity), mul_pos hx (show 0 < y ^ 2 by positivity), mul_pos hy (show 0 < x ^ 2 by positivity), mul_pos hy (show 0 < y ^ 2 by positivity)]

  have h9 : 0 ≤ (x ^ 2 + x * y + y ^ 2) / 3 := by
    nlinarith [sq_nonneg (x), sq_nonneg (y), mul_pos hx hy]

  have h10 : 0 ≤ (x + y) / 2 * sqrt ((x ^ 2 + y ^ 2) / 2) := by
    positivity

  nlinarith [Real.sqrt_nonneg ((x ^ 2 + y ^ 2) / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + y ^ 2) / 2 by positivity), sq_nonneg ((x + y) / 2 * sqrt ((x ^ 2 + y ^ 2) / 2) - (x ^ 2 + x * y + y ^ 2) / 3), h7]