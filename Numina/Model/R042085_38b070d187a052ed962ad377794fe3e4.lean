import Mathlib

open Real

theorem inequalities_156436 {x y : ℝ} (hy : y < x) (hxy : x * y = 1) :
    2 * sqrt 2 ≤ (x ^ 2 + y ^ 2) / (x - y) := by
  have h1 : x - y > 0 := by linarith
  have h2 : 2 * sqrt 2 * (x - y) ≤ x^2 + y^2 := by
    nlinarith [sq_nonneg (x - y - sqrt 2), sq_nonneg (x + y - 2 * sqrt 2), sq_nonneg (x^2 - y^2 - 2), sq_nonneg (x * y - 1), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), pow_two_nonneg (x - y), pow_two_nonneg (x * y), sq_nonneg (x^2 + y^2 - 4), sq_nonneg (x * y -1), hxy, sq_nonneg (x - (1 / y)), sq_nonneg (x + y), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h3 : 2 * sqrt 2 ≤ (x ^ 2 + y ^ 2) / (x - y) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith [h2]
  exact h3