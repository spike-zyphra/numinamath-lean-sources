import Mathlib

theorem number_theory_115143 :
    ∑ i ∈ Finset.range 2016, (2 : ℕ)^i = 2^2016 - 1 ∧
    15 ∣ 14 + 2^2016 := by
  constructor
  · native_decide
  · native_decide