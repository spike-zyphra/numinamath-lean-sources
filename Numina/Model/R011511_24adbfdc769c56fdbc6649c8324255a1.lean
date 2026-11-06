import Mathlib

theorem number_theory_13289 : (∑ i ∈ Finset.Icc 1 (2022), i^(1011)) % 10 = 9 := by
  native_decide