import Mathlib

theorem algebra_303652 {a : ℝ} (ha : a = (2 ^ ((1 : ℝ) / 3)) + 1) :
    (a^3 + a^4) / (a^3 + 1) = 3 := by
  have ha1 : a - 1 = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [ha]
    all_goals ring_nf
  -- Show ((a - 1) ^ 3) = 2
  have ha2 : ((a - 1) ^ 3) = 2 := by
    rw [ha1]
    have h1 : ((2: ℝ) ^ ((1: ℝ) / 3)) ^ 3 = (2: ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith [h1]
  -- Show $a ^ 3 = 3 * a ^ 2 - 3 * a + 3$
  have ha3 : a ^ 3 = 3 * a ^ 2 - 3 * a + 3 := by
    have h5 : (a - 1) ^ 3 = 2 := ha2
    ring_nf at h5 ⊢
    linarith
  -- Denominator not zero
  have h50 : a ^ 3 + 1 ≠ 0 := by
    nlinarith [ha2, show 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) by positivity, ha, sq_nonneg (a - 1), sq_nonneg (a^2 - a + 1), sq_nonneg (a + 1), sq_nonneg (a - 2), sq_nonneg (a ^ 2 - 1), Real.rpow_pos_of_pos (show 0 < (2 : ℝ) by norm_num) (1 / 3)]
  -- Numerator = 3 * Denominator
  have h7 : a ^ 3 + a ^ 4 = 3 * (a ^ 3 + 1) := by
    nlinarith [ha3, sq_nonneg (a - 1), sq_nonneg (a^2 - a + 1), sq_nonneg (a + 1), sq_nonneg (a - 2), sq_nonneg (a ^ 2 - 1)]
  -- Simplify Numerator and Denominator
  rw [h7]
  field_simp [h50]
  all_goals linarith [h50]