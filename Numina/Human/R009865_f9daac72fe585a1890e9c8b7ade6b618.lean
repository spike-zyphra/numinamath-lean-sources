import Mathlib

/- Simplify $\displaystyle\frac{1-i}{2+3i}$, where $i^2 = -1.$ -/
theorem algebra_11140 : (1 - Complex.I) / (2 + 3 * Complex.I) = -1 / 13 - 5 / 13 * Complex.I := by
  field_simp [Complex.ext_iff]
  norm_num