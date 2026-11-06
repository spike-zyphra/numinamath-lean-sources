import Mathlib

/- Simplify $\dfrac{5+12i}{2-3i}$. Your answer should be of the form $a+bi$, where $a$ and $b$ are both real numbers and written as improper fractions (if necessary). -/
theorem algebra_10308 : (5 + 12 * Complex.I) / (2 - 3 * Complex.I) = -2 + 3 * Complex.I := by 
  field_simp [Complex.ext_iff]
  norm_num