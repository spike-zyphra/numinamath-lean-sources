import Mathlib

theorem algebra_289713 : ∃ n : ℤ, (Real.sqrt 52 + 5) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5) ^ ((1 : ℝ) / 3) = n := by
  use 1
  have h1 : Real.sqrt 52 = Real.sqrt 52 := by rfl
  have h2 : (52 : ℝ) > 0 := by norm_num
  have h3 : Real.sqrt 52 > 0 := by positivity
  have h4 : (Real.sqrt 52 + 5 : ℝ) > 0 := by
    have h5 : Real.sqrt 52 > 0 := by positivity
    linarith
  have h5 : (Real.sqrt 52 - 5 : ℝ) > 0 := by
    have h6 : Real.sqrt 52 > (5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 52, Real.sq_sqrt (show (0 : ℝ) ≤ 52 by norm_num), sq_nonneg (Real.sqrt 52 - 5)]
    linarith
  have h7 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 52 + 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h8 : ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 52 - 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h9 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) = (3 : ℝ) := by
    have h10 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) = ((Real.sqrt 52 + 5 : ℝ) * (Real.sqrt 52 - 5 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow]
      all_goals nlinarith [Real.sqrt_nonneg 52, Real.sqrt_nonneg 52]
    rw [h10]
    have h11 : (Real.sqrt 52 + 5 : ℝ) * (Real.sqrt 52 - 5 : ℝ) = (27 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (52 : ℝ) by norm_num), sq_nonneg (Real.sqrt 52 - 5), Real.sqrt_nonneg 52]
    rw [h11]
    have h12 : (27 : ℝ) ^ ((1 : ℝ) / 3) = (3 : ℝ) := by
      have h13 : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [h13]
      have h14 : ((3 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (3 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith
    linarith
  have h13 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) = (1 : ℝ) := by
    have h14 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 10 - 3 * ( ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ) * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) := by
      have h15 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - 3 * ( ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ) * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) := by
        ring
      rw [h15, h7, h8]
      all_goals nlinarith [Real.sqrt_nonneg 52, Real.sq_sqrt (show (0 : ℝ) ≤ 52 by norm_num)]
    rw [h9] at h14
    have h15 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 9 * ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) - 10 = 0 := by
      nlinarith [h14]
    have h2 : ((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) - (1 : ℝ) = 0 := by
      nlinarith [sq_nonneg (((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) - (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) - 1), sq_nonneg (((Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3)) + ((Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3)) - 2), sq_nonneg (( (Real.sqrt 52 + 5 : ℝ) ^ ((1 : ℝ) / 3) ) * ( (Real.sqrt 52 - 5 : ℝ) ^ ((1 : ℝ) / 3) ) - 3), Real.sqrt_nonneg 52]
    linarith
  exact_mod_cast h13