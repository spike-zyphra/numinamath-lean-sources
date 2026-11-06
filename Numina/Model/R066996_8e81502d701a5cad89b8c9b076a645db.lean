import Mathlib

theorem number_theory_253535 : (∏ i ∈ Finset.Icc 101 200, i) % 2^100 = 0 ∧ ¬(2^101 ∣ ∏ i ∈ Finset.Icc 101 200, i) := by
  native_decide