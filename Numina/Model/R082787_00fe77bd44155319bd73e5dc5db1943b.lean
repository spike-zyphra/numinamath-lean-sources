import Mathlib

theorem number_theory_5084 : ∃ n, 0 < n ∧ (2011 : ℤ) ∣ (∑ i ∈ Finset.range n, 10^i) := by
  use 2010
  constructor
  · -- Show n is positive
    norm_num
  · -- Show divisibility
    native_decide