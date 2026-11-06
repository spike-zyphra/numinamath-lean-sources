import Mathlib

theorem algebra_188440 (x : ℝ) : x^3 + 3 * x^2 + 3 * x + 7 = 0 ↔
    x = -1 - 6 ^ ((1 : ℝ) / 3) := by 
  constructor
  · -- Assume x^3 + 3 * x^2 + 3 * x + 7 = 0, prove x = -1 - 6 ^ ((1 : ℝ) / 3)
    intro h
    have h1 : x^3 + 3 * x^2 + 3 * x + 7 = 0 := h
    have h2 : (x + 1) ^ 3 = -6 := by 
      nlinarith 
    have h3 : x + 1 = -6 ^ ((1 : ℝ) / 3) := by
      have h4 : ((x + 1) + (6 : ℝ) ^ ((1 : ℝ) / 3)) * (((x + 1) ^ 2) - ((x + 1) * (6 : ℝ) ^ ((1 : ℝ) / 3)) + ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) = 0 := by
        have h5 : ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (6 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals norm_num
        nlinarith [sq_nonneg ((x + 1) ^ 2), sq_nonneg ((6 : ℝ) ^ ((1 : ℝ) / 3) ^ 2), sq_nonneg ((x + 1) * (6 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((x + 1) * (x + 1)), sq_nonneg ((6 : ℝ) ^ ((1 : ℝ) / 3) * (6 : ℝ) ^ ((1 : ℝ) / 3)), Real.rpow_nonneg (show (0 : ℝ) ≤ (6 : ℝ) by norm_num) (1 / 3 : ℝ)]
      cases' (mul_eq_zero.mp h4) with h6 h7
      · -- Case where the first factor is zero, which gives the solution
        linarith
      · -- Case where the second factor is zero
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.rpow_nonneg (show (0 : ℝ) ≤ (6 : ℝ) by norm_num) (1 / 3 : ℝ), sq_nonneg ((6 : ℝ) ^ ((1 : ℝ) / 3) ^ 2), sq_nonneg ((x + 1) * (6 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((x + 1) * (6 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((6 : ℝ) ^ ((1 : ℝ) / 3) ^ 2), Real.rpow_pos_of_pos (show (0 : ℝ) < (6 : ℝ) by norm_num) (1 / 3 : ℝ)]
    have hx : x = -1 - 6 ^ ((1 : ℝ) / 3) := by
      nlinarith [h3]
    linarith [hx]
  · -- Assume x = -1 - 6 ^ ((1 : ℝ) / 3), prove x^3 + 3 * x^2 + 3 * x + 7 = 0
    intro h
    rw [h]
    have h2 : ((-1 - (6 : ℝ) ^ ((1 : ℝ) / 3) + 1 : ℝ) : ℝ) ^ 3 = -6 := by
      have h3 : ((6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (6 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals norm_num
      nlinarith [sq_nonneg ((-1 - (6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2), sq_nonneg ((6 : ℝ) ^ ((1 : ℝ) / 3) ^ 2), sq_nonneg ((-1 - (6 : ℝ) ^ ((1 : ℝ) / 3) + 1) * (6 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((-1 - (6 : ℝ) ^ ((1 : ℝ) / 3) + 1)), Real.rpow_nonneg (show (0 : ℝ) ≤ (6 : ℝ) by norm_num) (1 / 3 : ℝ)]
    nlinarith [sq_nonneg ((-1 - (6 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2), sq_nonneg ((6 : ℝ) ^ ((1 : ℝ) / 3) ^ 2), sq_nonneg ((-1 - (6 : ℝ) ^ ((1 : ℝ) / 3) + 1) * (6 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((-1 - (6 : ℝ) ^ ((1 : ℝ) / 3) + 1)), Real.rpow_nonneg (show (0 : ℝ) ≤ (6 : ℝ) by norm_num) (1 / 3 : ℝ)]