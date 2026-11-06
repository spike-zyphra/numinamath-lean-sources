import Mathlib

theorem number_theory_187925 :
    (∏ i ∈ Finset.range 50, (2 * i + 1)) % 10 = 5 ∧
    (∏ i ∈ Finset.range 100, (2 * i + 1)) % 10 = 5 := by
  native_decide