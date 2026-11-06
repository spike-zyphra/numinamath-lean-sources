import Mathlib

theorem algebra_141590 : (2^3 * 3^(-9 : ℤ) * 6^6 * 8^(-8 : ℤ) * 1728 : ℝ) = 2^(-9 : ℤ) := by
  norm_num [zpow_neg, zpow_ofNat, show (6 : ℝ) = 2 * 3 by norm_num, show (8 : ℝ) = 2^3 by norm_num, show (1728 : ℝ) = (2^2 * 3)^3 by norm_num]