import Mathlib

/- What is the value of 2^3−1^3+4^3−3^3+6^3−5^3+⋯+18^3−17^3?
(A) 2023(B) 2679(C) 2941(D) 3159(E) 3235 -/
theorem algebra_95560 : ∑ i ∈ Finset.range 9, ((2 * i + 2)^3 - (2 * i + 1)^3) = 3159 := by
    --solve by explicit computation
    ring_nf