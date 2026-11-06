import Mathlib

theorem number_theory_117350 : (∑ i ∈ Finset.Icc 1 2016, (i * 10 + 2) ^ (i * 10 + 2)) % 10 = 0 := by
  native_decide