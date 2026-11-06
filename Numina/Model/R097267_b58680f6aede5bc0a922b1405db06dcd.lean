import Mathlib

theorem number_theory_158060 : ∃ n, ∃ m, ∑ i ∈ Finset.range 13, (n + i) = m ^ 2021 := by
  use 13 ^ 2020 - 6
  use 13
  native_decide