import Mathlib

open Finset

/- Consider the integer $$N = 9 + 99 + 999 + 9999 + \cdots + \underbrace{99\ldots 99}_\text{321 digits}.$$ Find the sum of the digits of $N$. -/
theorem number_theory_80434 : (Nat.digits 10 (∑ i ∈ range 321, (10^(i + 1) - 1))).sum = 342 := by native_decide
