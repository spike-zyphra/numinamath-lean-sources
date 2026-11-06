import Mathlib

/- Find $\left(\frac{1}{2}\right)^{8} \cdot \left(\frac{3}{4}\right)^{-3}$. -/
theorem algebra_14895 : (1 / 2 : ℝ)^8 * (3 / 4)^(-3 : ℤ) = 1 / 108 := by
  norm_num [zpow_ofNat]