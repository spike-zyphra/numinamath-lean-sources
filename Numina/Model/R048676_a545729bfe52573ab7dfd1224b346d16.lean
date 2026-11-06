import Mathlib

theorem number_theory_238867 (n : ℕ) (hn : n = 2017) :
    ∃ a : Fin n → ℤ, (∑ i, a i = 2018) ∧ (∏ i, a i = 2018) ∧ 2018 ∈ Set.range a := by
  rw [hn]
  use fun i =>
    if i = 0 then
      2018
    else
      if i % 2 = 1 then
        1
      else
        -1
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide