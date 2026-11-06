import Mathlib

/- Divide the reciprocal of $\frac{5}{6}$ by the reciprocal of the reciprocal of $\frac{5}{6}$. -/
theorem algebra_21714 : (5 / 6 : ℚ)⁻¹ / (5 / 6)⁻¹⁻¹ = 36 / 25 := by norm_num
