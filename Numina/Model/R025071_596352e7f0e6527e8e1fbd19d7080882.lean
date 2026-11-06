import Mathlib

theorem algebra_301345 : ((Real.sqrt 5 - 1) / 2 - ((Real.sqrt 5 - 1) / 2)^2) ^ ((1 : ℝ) / 3) = (Real.sqrt 5 - 1) / 2 := by
  have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : ((Real.sqrt 5 - 1) / 2 - ((Real.sqrt 5 - 1) / 2) ^ 2) = Real.sqrt 5 - 2 := by
    nlinarith [h1, Real.sqrt_nonneg 5, sq_nonneg (Real.sqrt 5 - 1)]
  have h3 : ((Real.sqrt 5 - 1) / 2) ^ 3 = Real.sqrt 5 - 2 := by
    ring_nf
    nlinarith [h1, Real.sqrt_nonneg 5, sq_nonneg (Real.sqrt 5 - 1), sq_nonneg (Real.sqrt 5 ^ 2 - 5)]
  have h4 : (Real.sqrt 5 - 2 : ℝ) = ((Real.sqrt 5 - 1) / 2) ^ 3 := by linarith [h3]
  rw [h2]
  rw [h4]
  have h7 : ( ((Real.sqrt 5 - 1) / 2) ^ 3) ^ ((1 : ℝ) / 3) = (Real.sqrt 5 - 1) / 2 := by
    have h8 : ( ((Real.sqrt 5 - 1) / 2) ^ 3 ) ^ ((1 : ℝ) / 3) = ( (Real.sqrt 5 - 1) / 2 ) := by
      have h9 : ( (Real.sqrt 5 - 1) / 2 ) ^ 3 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 5, h1, sq_nonneg (Real.sqrt 5 - 1)]
      have h10 : (( (Real.sqrt 5 - 1) / 2 ) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = ( (Real.sqrt 5 - 1) / 2 ) := by
        have h12 : ( (Real.sqrt 5 - 1) / 2 ) ^ 3 ≥ 0 := h9
        have h13 : (( (Real.sqrt 5 - 1) / 2 ) ^ 3 ) ^ ((1 : ℝ) / 3) = ( (Real.sqrt 5 - 1) / 2 ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals nlinarith
        nlinarith
      nlinarith
    linarith
  linarith [h7, Real.sqrt_nonneg 5, h1, sq_nonneg (Real.sqrt 5 - 1)]