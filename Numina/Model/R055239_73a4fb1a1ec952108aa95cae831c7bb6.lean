import Mathlib

theorem algebra_221610 : ∑ i ∈ Finset.range 2001, (i + 1) * 2 ^ (i : ℕ) = 2000 * 2 ^ 2001 + 1 := by 
  native_decide