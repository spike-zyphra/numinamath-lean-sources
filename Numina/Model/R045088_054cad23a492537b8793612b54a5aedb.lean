import Mathlib

theorem algebra_22386 (a b c : ℝ) (ha : a = 2 ^ ((2 : ℝ) / 3)) (hb : b = 2 ^ ((1 : ℝ) / 3))
    (hc : c = 2 - 2 * b - a) :
    (a + b) * c = -6 := by
  have h1 : a = b ^ 2 := by
    rw [ha, hb]
    have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    exact h2
  rw [hc, h1]
  have h2 : b ^ 3 = (2 : ℝ) := by
    rw [hb]
    have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    exact h3
  have h3 : b ^ 4 = 2 * b := by
    calc
      b ^ 4 = b * (b ^ 3) := by ring
      _ = b * (2) := by rw [h2]
      _ = 2 * b := by ring
  nlinarith [sq_nonneg (b ^ 2 - 2), sq_nonneg (b - 1), sq_nonneg (b + 1), sq_nonneg (b ^ 2 - 2 * b), sq_nonneg (b ^ 3 - 2), sq_nonneg (b ^ 2 - 2), h2, h3, sq_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]