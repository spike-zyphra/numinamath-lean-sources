import Mathlib

theorem number_theory_93369 : ∃ k, 1627384950 = ∑ i ∈ Finset.range 100, ((k + 1) + i) := by
  use 16273799
  native_decide