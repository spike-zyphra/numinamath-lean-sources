import Mathlib

open Real
theorem algebra_95336 {f : ℕ → ℝ} (hf : ∀ n, f n = logb 2002 (n ^ 2)) : f 11 + f 13 + f 14 = 2 := by 
  have h11 : f 11 = logb 2002 (11 ^ 2) := hf 11 
  have h13 : f 13 = logb 2002 (13 ^ 2) := hf 13 
  have h14 : f 14 = logb 2002 (14 ^ 2) := hf 14 
  rw [h11, h13, h14]
  have h2 : logb 2002 (11 ^ 2 : ℝ) + logb 2002 (13 ^ 2 : ℝ) + logb 2002 (14 ^ 2 : ℝ) = logb 2002 ((11 ^ 2 : ℝ) * (13 ^ 2 : ℝ) * (14 ^ 2 : ℝ)) := by 
    rw [← logb_mul (by norm_num) (by norm_num), ← logb_mul (by norm_num) (by norm_num)]
  rw [h2]
  have h3 : (11 ^ 2 : ℝ) * (13 ^ 2 : ℝ) * (14 ^ 2 : ℝ) = (2002 : ℝ) ^ 2 := by
    norm_num
  rw [h3]
  have h4 : logb 2002 ((2002 : ℝ) ^ 2) = (2 : ℝ) := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  rw [h4]