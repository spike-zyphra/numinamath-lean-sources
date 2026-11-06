import Mathlib


theorem algebra_13379 : ∃ x : ℝ, Real.rpow 2 x + 6 = 3 * Real.rpow 2 x - 26 := by
  use 4
  -- 展开并验证等式： 2^4 + 6 = 48 - 26 = 16 + 6 = 48 - 26
  norm_num
