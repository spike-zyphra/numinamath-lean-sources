import Mathlib

theorem number_theory_177233 (n : ℕ) :
    ∃ x > 0, n = 2^(2*x - 1) - 5*x - 3 ∧ n = (2^(x - 1) - 1)*(2^x + 1) ↔ n = 2015 := by
  use 6
  constructor
  · norm_num
  · -- Assume that n = 2^(2*6 - 1) - 5*6 - 3 and n = (2^(6 - 1) - 1)*(2^6 + 1), prove that n = 2015
    constructor
    · -- Assume n = 2^(2*6 - 1) - 5*6 - 3 ∧ n = (2^(6 - 1) - 1)*(2^6 + 1), prove n = 2015
      norm_num
      all_goals tauto
    · -- Assume n = 2015, prove n = 2^(2*6 - 1) - 5*6 - 3 ∧ n = (2^(6 - 1) - 1)*(2^6 + 1)
      intro h
      rw [h]
      constructor
      · -- Compute n = 2^(2*6 - 1) - 5*6 - 3
        norm_num
      · -- Compute n = (2^(6 - 1) - 1)*(2^6 + 1)
        norm_num