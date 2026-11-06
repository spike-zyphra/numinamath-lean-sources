import Mathlib

theorem number_theory_1382 : (2 ^ 2005 - 1) = ∑ i ∈ Finset.range 2005, (1 : ℕ) * 2 ^ i := by
  native_decide