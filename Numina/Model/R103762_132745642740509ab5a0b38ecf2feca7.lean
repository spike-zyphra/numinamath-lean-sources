import Mathlib

open Real

theorem algebra_13912 (f : ℕ → ℝ) (hf : ∀ n, 0 < n → f n = logb 2002 (n ^ 2)) :
    f 11 + f 13 + f 14 = 2 := by
  have h11 : f 11 = logb 2002 (11 ^ 2) := hf 11 (by norm_num)
  have h13 : f 13 = logb 2002 (13 ^ 2) := hf 13 (by norm_num)
  have h14 : f 14 = logb 2002 (14 ^ 2) := hf 14 (by norm_num)
  rw [h11, h13, h14]
  have h1 : logb 2002 (11 ^ 2 : ℝ) + logb 2002 (13 ^ 2 : ℝ) + logb 2002 (14 ^ 2 : ℝ) = logb 2002 ((11 : ℝ) ^ 2 * (13 : ℝ) ^ 2 * (14 : ℝ) ^ 2) := by
    simp [logb_mul]
    all_goals norm_num
  have h2 : ((11 : ℝ) ^ 2 * (13 : ℝ) ^ 2 * (14 : ℝ) ^ 2) = (2002 : ℝ) ^ 2 := by norm_num
  rw [h1, h2]
  simp [logb_pow]
  all_goals norm_num