import Mathlib

/- The expression $\dfrac{\sqrt[3]{5}}{\sqrt[5]{5}}$ equals 5 raised to what power?-/
theorem algebra_14598 : (5 : ℝ) ^ ((1 : ℝ) / 3) / 5 ^ ((1 : ℝ) / 5) = 5 ^ ((2 : ℝ) / 15) := by
  -- transform the division into a subtraction in the exponent
  rw [← Real.rpow_sub (by norm_num)]
  -- trivial calculation
  norm_num