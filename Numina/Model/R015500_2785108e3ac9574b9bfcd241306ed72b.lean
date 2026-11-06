import Mathlib

open Real

theorem inequalities_297073 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x * y / sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) ≤ 1 / (1 + sqrt 3) := by
  have h1 : 0 < x ^ 2 := by
    nlinarith
  have h2 : 0 < y ^ 2 := by
    nlinarith
  have h3 : 0 < (x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2) := by
    positivity
  have h4 : sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) > 0 := by
    apply Real.sqrt_pos.mpr
    positivity
  have h5 : 1 + Real.sqrt 3 > 0 := by
    have h6 : 0 < Real.sqrt 3 := by
      positivity
    linarith
  have h7 : x * y / sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) ≤ 1 / (1 + sqrt 3) := by
    have h8 : x * y * (1 + Real.sqrt 3) ≤ sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) := by
      have h9 : (x * y * (1 + Real.sqrt 3)) ^ 2 ≤ (x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2) := by
        nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y), Real.sqrt_pos.mpr (show (3: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (3 * x ^ 2 - y ^ 2), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), mul_nonneg (show 0 ≤ x ^ 2 by positivity) (show 0 ≤ y ^ 2 by positivity), sq_nonneg (sqrt 3 * x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - sqrt 3 * y ^ 2), mul_nonneg (Real.sqrt_nonneg 3) (show 0 ≤ y ^ 2 by positivity), mul_nonneg (Real.sqrt_nonneg 3) (show 0 ≤ x ^ 2 by positivity), sq_nonneg (x * y * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h10 : sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) ≥ 0 := by
        positivity
      have h11 : (x * y * (1 + Real.sqrt 3)) ^ 2 ≤ (sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2))) ^ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2) by positivity)]
      have h12 : (x * y * (1 + Real.sqrt 3)) ≥ 0 := by
        positivity
      have h13 : sqrt ((x * y * (1 + Real.sqrt 3)) ^ 2) ≤ sqrt ((sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h14 : sqrt ((x * y * (1 + Real.sqrt 3)) ^ 2) = x * y * (1 + Real.sqrt 3) := by
        rw [Real.sqrt_sq (by
          positivity
        )]
      have h15 : sqrt ((sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2))) ^ 2) = sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) := by
        rw [Real.sqrt_sq (by
          positivity
        )]
      nlinarith [h14, h15, h13]
      all_goals nlinarith
    have h9 : 0 < sqrt ((x ^ 2 + y ^ 2) * (3 * x ^ 2 + y ^ 2)) := h4
    have h10 : 0 < 1 + Real.sqrt 3 := h5
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h8]
  exact h7