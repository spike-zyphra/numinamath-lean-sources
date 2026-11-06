import Mathlib
open Real

theorem algebra_8761 : (logb 2 3 ^ 3 - logb 2 6 ^ 3 - logb 2 12 ^ 3 + logb 2 24 ^ 3) / 6 = logb 2 72 := by
  have h1 : logb 2 6 = 1 + logb 2 3 := by
    calc
      logb 2 6 = logb 2 (2 * 3) := by norm_num
      _ = logb 2 2 + logb 2 3 := by rw [logb_mul (by norm_num) (by norm_num)]
      _ = 1 + logb 2 3 := by simp [logb_self_eq_one]

  have h2 : logb 2 12 = 2 + logb 2 3 := by
    calc
      logb 2 12 = logb 2 (2^2 * 3) := by norm_num
      _ = logb 2 (2^2) + logb 2 3 := by rw [logb_mul (by norm_num) (by norm_num)]
      _ = 2 * logb 2 2 + logb 2 3 := by simp [logb_pow]
      _ = 2 * 1 + logb 2 3 := by rw [logb_self_eq_one]; all_goals linarith
      _ = 2 + logb 2 3 := by ring

  have h3 : logb 2 24 = 3 + logb 2 3 := by
    calc
      logb 2 24 = logb 2 (2^3 * 3) := by norm_num
      _ = logb 2 (2^3) + logb 2 3 := by rw [logb_mul (by norm_num) (by norm_num)]
      _ = 3 * logb 2 2 + logb 2 3 := by simp [logb_pow]
      _ = 3 * 1 + logb 2 3 := by rw [logb_self_eq_one]; all_goals linarith
      _ = 3 + logb 2 3 := by ring

  have h4 : logb 2 72 = 3 + 2 * logb 2 3 := by
    calc
      logb 2 72 = logb 2 (2^3 * 3^2) := by norm_num
      _ = logb 2 (2^3) + logb 2 (3^2) := by rw [logb_mul (by norm_num) (by norm_num)]
      _ = 3 * logb 2 2 + 2 * logb 2 3 := by simp [logb_pow]
      _ = 3 * 1 + 2 * logb 2 3 := by rw [logb_self_eq_one]; all_goals linarith
      _ = 3 + 2 * logb 2 3 := by ring

  rw [h1, h2, h3, h4]
  ring_nf
  <;> field_simp
  <;> ring_nf
  <;> norm_num [logb_eq_iff_rpow_eq]
  <;> ring
  <;> nlinarith [sq_nonneg (logb 2 3), sq_nonneg (logb 2 3 - 1), sq_nonneg (logb 2 3 - 2)]
  all_goals linarith [sq_nonneg (logb 2 3 - 2), sq_nonneg (logb 2 3), sq_nonneg (logb 2 3 - 1)]
  all_goals nlinarith
  all_goals ring_nf
  all_goals nlinarith
  all_goals tauto