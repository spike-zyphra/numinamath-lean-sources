import Mathlib

/- What is the sum of all integers $x$ for which $-30 \leq x \leq 26$ ? -/
theorem algebra_19904 : ∑ x in Finset.Icc (-30) 26, x = -114 := by 
  rfl