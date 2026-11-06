import Mathlib

open Real

theorem inequalities_165235 : sqrt 11 - sqrt 5 > sqrt 19 - sqrt 11 := by
  have h1 : sqrt 11 > 0 := by positivity
  have h2 : sqrt 5 > 0 := by positivity
  have h3 : sqrt 19 > 0 := by positivity
  have h4 : sqrt 11 - sqrt 5 > sqrt 19 - sqrt 11 := by
    have h5 : sqrt 11 + sqrt 11 > sqrt 19 + sqrt 5 := by
      have h6 : 0 < sqrt 19 + sqrt 5 := by
        have h7 : sqrt 19 > 0 := by positivity
        have h8 : sqrt 5 > 0 := by positivity
        linarith
      have h7 : (sqrt 11 + sqrt 11) ^ 2 > (sqrt 19 + sqrt 5) ^ 2 := by
        have h8 : (sqrt 11 + sqrt 11) ^ 2 = 44 := by
          have h9 : sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
          nlinarith
        have h9 : (sqrt 19 + sqrt 5) ^ 2 = (sqrt 19) ^ 2 + (sqrt 5) ^ 2 + 2 * (sqrt 19 * sqrt 5) := by ring
        have h10 : (sqrt 19) ^ 2 = 19 := Real.sq_sqrt (by norm_num)
        have h11 : (sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        have h12 : sqrt 19 * sqrt 5 = sqrt 95 := by
          rw [← Real.sqrt_mul (by norm_num)]
          all_goals norm_num
        nlinarith [h8, h9, h10, h11, h12, Real.sqrt_nonneg 95, Real.sq_sqrt (show 0 ≤ (95 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_nonneg 11, Real.sqrt_nonneg 19, Real.sqrt_nonneg 5]
    nlinarith [Real.sqrt_nonneg 11, Real.sqrt_nonneg 5, Real.sqrt_nonneg 19, Real.sqrt_nonneg 11]
  linarith [h4, Real.sqrt_nonneg 11, Real.sqrt_nonneg 5, Real.sqrt_nonneg 19, Real.sqrt_nonneg 11]