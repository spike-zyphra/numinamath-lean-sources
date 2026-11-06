import Mathlib

theorem number_theory_4733 :
    ∃ n, 206750 = ∑ i ∈ Finset.range 100, (n + i) ∧ n = 2018 := by
  use 2018
  constructor
  · -- prove 206750 = sum
    native_decide
  · -- prove n = 2018
    rfl