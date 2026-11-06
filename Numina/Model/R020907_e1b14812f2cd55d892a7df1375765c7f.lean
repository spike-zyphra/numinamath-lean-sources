import Mathlib

open Real

theorem inequalities_40569 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (a : ℝ) :
    x ^ sin a ^ 2 * y ^ cos a ^ 2 < x + y := by 
  have h1 : sin a ^ 2 + cos a ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq a
  have h2 : x ^ sin a ^ 2 * y ^ cos a ^ 2 ≤ sin a ^ 2 * x + cos a ^ 2 * y := by
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      try nlinarith [Real.sin_sq_add_cos_sq a, hx, hy]
      all_goals
        try positivity
        all_goals
          nlinarith [Real.sin_sq_add_cos_sq a]
  have h3 : sin a ^ 2 * x + cos a ^ 2 * y < x + y := by 
    nlinarith [h1, mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (sin a ^ 2 - cos a ^ 2), sq_pos_of_pos hx, sq_pos_of_pos hy, Real.sin_sq_add_cos_sq a]
  nlinarith [h2, h3, Real.rpow_pos_of_pos hx (sin a ^ 2), Real.rpow_pos_of_pos hy (cos a ^ 2), mul_nonneg (show 0 ≤ sin a ^ 2 by nlinarith [sq_nonneg (sin a)]) (show 0 ≤ cos a ^ 2 by nlinarith [sq_nonneg (cos a)]), Real.sin_sq_add_cos_sq a]