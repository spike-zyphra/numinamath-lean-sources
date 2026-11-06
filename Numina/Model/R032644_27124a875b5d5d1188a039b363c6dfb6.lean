import Mathlib

theorem number_theory_121367 : ∑ i ∈ Finset.range 1001, (2 ^ i / 3 : ℕ) = (2 ^ 1001 - 2 : ℚ) / 3 - 500 := by
  native_decide