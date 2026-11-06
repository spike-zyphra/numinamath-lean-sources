import Mathlib

/- Prove that the product of the first $1000$ positive even integers differs from the product of the first $1000$ positive odd integers by a multiple of $2001$. -/
theorem number_theory_67069 :
    ∏ i ∈ Finset.range 1000, (2 * i + 2) ≡ ∏ i ∈ Finset.range 1000, (2 * i + 1) [MOD 2001] := by native_decide
