import Mathlib

open Real

theorem algebra_186839 : sqrt (3 + sqrt 5) - sqrt (3 - sqrt 5) = sqrt 2 := by
  have h1 : sqrt (3 + sqrt 5) - sqrt (3 - sqrt 5) ≥ 0 := by 
    have h2 : sqrt (3 + sqrt 5) ≥ sqrt (3 - sqrt 5) := by
      apply Real.sqrt_le_sqrt
      have h5 : sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
      have h3 : sqrt 5 ≤ 3 := by
        have h5' : sqrt 5 < 3 := by
          rw [Real.sqrt_lt] <;> norm_num
        linarith
      nlinarith
    linarith
  have h2 : (sqrt (3 + sqrt 5) - sqrt (3 - sqrt 5)) ^ 2 = 2 := by
    have h3 : (sqrt (3 + sqrt 5) - sqrt (3 - sqrt 5)) ^ 2 = 
      (sqrt (3 + sqrt 5)) ^ 2 + (sqrt (3 - sqrt 5)) ^ 2 - 2 * (sqrt (3 + sqrt 5) * sqrt (3 - sqrt 5)) := by ring
    have h4 : (sqrt (3 + sqrt 5)) ^ 2 = 3 + sqrt 5 := by
      exact Real.sq_sqrt (by linarith [Real.sqrt_nonneg 5])
    have h30 : (3 - sqrt 5) ≥ 0 := by
      have h5 : sqrt 5 ≤ 3 := by
        have h5' : sqrt 5 < 3 := by 
          rw [Real.sqrt_lt] <;> norm_num
        linarith
      linarith
    have h5 : (sqrt (3 - sqrt 5)) ^ 2 = 3 - sqrt 5 := by
      exact Real.sq_sqrt (by
        nlinarith [Real.sqrt_nonneg 5]
      )
    have h6 : sqrt (3 + sqrt 5) * sqrt (3 - sqrt 5) = sqrt ((3 + sqrt 5) * (3 - sqrt 5)) := by
      rw [← Real.sqrt_mul (by
        have h31 : (3 + sqrt 5) ≥ 0 := by linarith [Real.sqrt_nonneg 5]
        have h32 : (3 - sqrt 5) ≥ 0 := by 
          have h5 : sqrt 5 ≤ 3 := by
            have h5' : sqrt 5 < 3 := by
              rw [Real.sqrt_lt] <;> norm_num
            linarith
          linarith
        linarith
      )]
    have h7 : (3 + sqrt 5) * (3 - sqrt 5) = 4 := by
      nlinarith [Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    have h8 : sqrt ((3 + sqrt 5) * (3 - sqrt 5)) = 2 := by
      rw [h7]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3]
    rw [h4, h5, h6, h8]
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg (3 + sqrt 5), Real.sqrt_nonneg (3 - sqrt 5)]
  have h21 : sqrt (3 + sqrt 5) - sqrt (3 - sqrt 5) = Real.sqrt ((sqrt (3 + sqrt 5) - sqrt (3 - sqrt 5)) ^ 2) := by
    rw [Real.sqrt_sq (by linarith [h1])]
  have h22 : Real.sqrt ((sqrt (3 + sqrt 5) - sqrt (3 - sqrt 5)) ^ 2) = Real.sqrt 2 := by 
    rw [h2]
  rw [h22] at h21
  linarith [h21]