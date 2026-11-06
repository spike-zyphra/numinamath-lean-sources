import Mathlib

theorem number_theory_40495 : ∑ i ∈ Finset.range 100, (i + 1) * (i + 2) / 2 = 171700 := by
  native_decide