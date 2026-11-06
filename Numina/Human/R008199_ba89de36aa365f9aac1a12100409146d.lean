import Mathlib

set_option exponentiation.threshold 2009
set_option maxRecDepth 10000

/- What is the ones digit of $1^{2009} + 2^{2009} + 3^{2009} + \cdots + 2009^{2009}?$ -/
theorem number_theory_15394 : (∑ i in Finset.Icc 1 2009, i^2009) % 10 = 5 := by
  rfl
