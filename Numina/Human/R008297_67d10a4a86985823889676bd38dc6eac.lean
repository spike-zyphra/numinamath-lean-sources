import Mathlib

/- Show that $\left(\frac{2010}{2009}\right)^{2009}> 2$. -/
theorem inequalities_45712 : (2010 / 2009 : ℝ)^2009 > 2 := by
  -- Normalize fractions in the expression and verify numerical constants.
  norm_num