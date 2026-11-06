import Mathlib

/- Solve for $c$: \[\frac{c-23}{2} = \frac{2c +5}{7}.\] -/
theorem algebra_12200 {c : ℝ} (h : (c - 23) / 2 = (2 * c + 5) / 7) : c = 57 := by
  field_simp at h
  linarith