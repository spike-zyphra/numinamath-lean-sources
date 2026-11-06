import Mathlib

/- Compute
\[\frac{1}{2^3 - 2} + \frac{1}{3^3 - 3} + \frac{1}{4^3 - 4} + \dots + \frac{1}{100^3 - 100}.\] -/
theorem algebra_21197 : ∑ i ∈ Finset.Icc (2 : ℕ) 100, (1 / ((i : ℚ)^3 - i)) = 5049 / 20200 := by
  native_decide
