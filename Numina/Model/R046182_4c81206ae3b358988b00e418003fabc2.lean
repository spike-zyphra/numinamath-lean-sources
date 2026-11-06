import Mathlib

theorem algebra_249663 {M : ℝ} (hM : M = (√5 + 2) ^ ((1 : ℝ) / 3) - (√5 - 2) ^ ((1 : ℝ) / 3)) :
    ∃ n : ℤ, M = n := by
  use 1
  have h1 : M = 1 := by
    rw [hM]
    have h2 : ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)) - 4 = (0 : ℝ) := by
      have h11 : ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = √5 + 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num : (5 : ℝ) ≥ 0)]
      have h12 : ((√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = √5 - 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num : (5 : ℝ) ≥ 0)]
      have h13 : ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3)) * ((√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)) = 1 := by
        have h11 : ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3)) * ((√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)) = ((√5 + 2 : ℝ) * (√5 - 2 : ℝ)) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow]
          all_goals
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num : (5 : ℝ) ≥ 0)]
        rw [h11]
        have h14 : ((√5 + 2 : ℝ) * (√5 - 2 : ℝ)) = (1 : ℝ) := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num : (5 : ℝ) ≥ 0)]
        rw [h14]
        norm_num
      nlinarith [sq_nonneg ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) + (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3) ), sq_nonneg ((√5) ^ 2 - 4)]
    have h3 : ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3) - 1) * (((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3)) + 4) = 0 := by 
      nlinarith [h2]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case $M - 1 = 0$, so $M = 1$:
      linarith
    · -- Case $M^2 + M + 4 = 0$:
      nlinarith [sq_nonneg ((√5 + 2 : ℝ) ^ ((1 : ℝ) / 3) - (√5 - 2 : ℝ) ^ ((1 : ℝ) / 3) + 1 / 2)]
  rw [h1]
  all_goals norm_num