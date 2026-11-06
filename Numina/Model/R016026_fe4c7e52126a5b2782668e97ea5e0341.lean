import Mathlib

theorem algebra_10846 : round ((6 ^ 3 + 8 ^ 3 : ℝ) ^ ((1 : ℝ) / 3)) = 9 := by
  have h1 : (6 ^ 3 + 8 ^ 3 : ℝ) = (728 : ℝ) := by norm_num
  rw [h1]
  have h2 : (728 : ℝ) ^ ((1 : ℝ) / 3) > (8.5 : ℝ) := by
    have h7 : ( (8.5 : ℝ) ) ^ 3 < (728 : ℝ) := by norm_num
    have h8 : ( (728 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (728 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    nlinarith [sq_nonneg ( (728 : ℝ) ^ ((1 : ℝ) / 3) - (8.5 : ℝ) ), sq_nonneg ( ( (8.5 : ℝ) ^ 2 ) ), sq_nonneg ( ( (728 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 - ( (8.5 : ℝ) ) ^ 2 ), Real.rpow_nonneg (show (0 : ℝ) ≤ (728 : ℝ) by norm_num) (1 / 3)]
  have h3 : (728 : ℝ) ^ ((1 : ℝ) / 3) < (9.5 : ℝ) := by
    have h4 : (728 : ℝ) < (9.5 : ℝ) ^ 3 := by norm_num
    have h5 : ( (728 : ℝ) ^ ((1 : ℝ) / 3) ) < (9.5 : ℝ) := by
      have h6 : ( (728 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (728 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      nlinarith [sq_nonneg ( (9.5 : ℝ) - ( (728 : ℝ) ^ ((1 : ℝ) / 3) ) ), sq_nonneg ( ( (728 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 - ( (9.5 : ℝ) ) ^ 2 ), sq_nonneg ( ( (9.5 : ℝ) ) ^ 2 ), Real.rpow_nonneg (show (0 : ℝ) ≤ (728 : ℝ) by norm_num) (1 / 3) ]
    linarith
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith