import Mathlib

theorem number_theory_12361 : ∃ k, 2016 ∈ Finset.Icc (1 + ∑ i in Finset.range k, (i + 1)) (1 + ∑ i in Finset.range (k + 1), (i + 1)) := by
  use 62
  native_decide