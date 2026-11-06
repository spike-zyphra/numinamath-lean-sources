import Mathlib

/- Find $\left(\frac{8}{9} \cdot \left(\frac{1}{2}\right)^4\right)^{-1} - 17$. -/
theorem algebra_21018 : ((8 / 9 : ℝ) * (1 / 2)^4)^(-1 : ℤ) - 17 = 1 := by
  norm_num