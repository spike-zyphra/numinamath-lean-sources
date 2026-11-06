import Mathlib

theorem algebra_286811 (x : ℝ) (hx : x = (Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) :
    ∃ q : ℚ, x = q := by
  use 1
  have ha1 : x = 1 := by
    rw [hx]
    have h1 : ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) - 4 = 0 := by
      have h2 : ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 5 + 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      have h3 : ((Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) ^ 3 = Real.sqrt 5 - 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          have h4 : Real.sqrt 5 ≥ 2 := by
            have h1 : Real.sqrt 5 ≥ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
            have h2 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
            linarith
          have h5 : Real.sqrt 5 - 2 ≥ 0 := by linarith [h4]
          linarith [h5, Real.sqrt_nonneg 5]
      have h6 : ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) = 1 := by
        have h7 : ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3)) * ((Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) =
          ((Real.sqrt 5 + 2) * (Real.sqrt 5 - 2)) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow]
          all_goals
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        rw [h7]
        have h8 : (Real.sqrt 5 + 2) * (Real.sqrt 5 - 2) = 1 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        rw [h8]
        have h9 : ((1 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
          simp
        rw [h9]
      nlinarith [h2, h3, h6, sq_nonneg ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)), sq_nonneg ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) + (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)), Real.sqrt_nonneg 5]
    have h9 : ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3) - (1 : ℝ)) * (((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) ^ 2 + ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Case where x - 1 = 0
      linarith
    · -- Case where the quadratic factor is zero
      have h12 : ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) ^ 2 + ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)) + 4 > 0 := by
        nlinarith [sq_nonneg ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) - (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)), sq_nonneg ((Real.sqrt 5 + 2) ^ ((1 : ℝ) / 3) + (Real.sqrt 5 - 2) ^ ((1 : ℝ) / 3)), Real.sqrt_nonneg 5]
      nlinarith [h11, h12]
  rw [ha1]
  norm_num