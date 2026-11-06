import Mathlib

/- Find the value of the sum
\[\binom{99}{0} - \binom{99}{2} + \binom{99}{4} - \dots - \binom{99}{98}.\] -/
theorem algebra_16826 : ∑ i ∈ Finset.range 50, (-1 : ℤ)^i * Nat.choose 99 (2 * i) = -2^49 := by native_decide
