import Mathlib

theorem algebra_145207 : (0.4 : ℝ)^(-2 : ℤ) * (2 + 1 / 4 : ℝ)^(-1 : ℤ) / ((-1 / 3 : ℝ)^3 * 0.1^(-2 : ℤ)) = -3 / 4 := by
  norm_num [zpow_neg, zpow_ofNat]