import Mathlib

theorem number_theory_300893 : ∃ n, 2013 ∈ Finset.Icc (n * (n - 1) + 1) (n * n - 1) := by
  use 45
  native_decide