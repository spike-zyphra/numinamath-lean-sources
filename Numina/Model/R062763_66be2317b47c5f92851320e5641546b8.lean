import Mathlib

theorem algebra_184151 : (2^(-2 : ℤ) + 5^0 : ℝ) / ((0.5)^(-2 : ℤ) - 5 * (-2 : ℝ)^(-2 : ℤ) + (2 / 3)^(-2 : ℤ)) + 4.75 = 5 := by
  norm_num [zpow_neg, zpow_ofNat, zpow_zero]