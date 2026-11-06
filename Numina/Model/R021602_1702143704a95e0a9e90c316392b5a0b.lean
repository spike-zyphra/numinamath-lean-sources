import Mathlib

theorem number_theory_109020 : (2^2021 - 1) = ∑ i ∈ Finset.range 2021, 2^i := by
  native_decide