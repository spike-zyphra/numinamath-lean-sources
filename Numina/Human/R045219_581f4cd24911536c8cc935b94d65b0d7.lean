import Mathlib

/- Simplify $\displaystyle\frac{2+2i}{-3+4i}$.  Express your answer as a complex number in the form $a+bi$, where $a$ and $b$ are real numbers. -/
theorem algebra_13816 : (2 + 2 * Complex.I) / (-3 + 4 * Complex.I) = 2 / 25 - 14 * Complex.I / 25 := by
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  ring
  norm_num