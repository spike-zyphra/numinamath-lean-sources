import Mathlib

/- Simplify $\dfrac{3+4i}{1+2i}$. Your answer should be of the form $a+bi$, where $a$ and $b$ are both real numbers and written as improper fractions (if necessary). -/
theorem algebra_14832 : (3 + 4 * .I : ℂ) / (1 + 2 * .I) = (11 / 5 - 2 / 5 * .I) := by
  field_simp [Complex.ext_iff]
  ring
  norm_num