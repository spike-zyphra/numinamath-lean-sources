import Mathlib

theorem algebra_220089 {a b c : ℝ} (h₀ : a - b = 2) (h₁ : a - c = 7 ^ ((1 : ℝ) / 3)) :
    (c - b) * ((a - b)^2 + (a - b) * (a - c) + (a - c)^2) = 1 := by
  have h2 : c - b = (2 - (7 : ℝ) ^ ((1 : ℝ) / 3)) := by
    have h3 : a = b + 2 := by linarith 
    have h4 : a = c + (7 : ℝ) ^ ((1 : ℝ) / 3) := by linarith 
    have h5 : c = b + (2 : ℝ) - (7 : ℝ) ^ ((1 : ℝ) / 3) := by 
      linarith [h3, h4]
    linarith [h5]
  rw [h2, h₀, h₁]
  -- From the previous substitution, we now have to prove
  -- (2 - 7^(1/3)) * (2^2 + 2 * 7^(1/3) + (7^(1/3)) ^ 2) = 1
  -- Using the difference of cubes formula: (x - y)(x^2 + xy + y^2) = x^3 - y^3
  -- Here x = 2 and y = 7^(1/3)
  -- 2^3 - (7^(1/3))^3 = 8 - 7 = 1
  have h3 : ((7 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num
  nlinarith [sq_nonneg ((2: ℝ) - (7 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ((7: ℝ) ^ ((1 : ℝ) / 3) - 2), sq_nonneg ((7 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg (2 - (7 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg ( (7 : ℝ) ^ ((1 : ℝ) / 3) + 2 ), sq_nonneg ( (7 : ℝ) ^ ((1 : ℝ) / 3) - (2 : ℝ) ), h3]