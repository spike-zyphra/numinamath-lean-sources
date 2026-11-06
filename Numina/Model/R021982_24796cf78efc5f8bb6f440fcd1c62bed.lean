import Mathlib

theorem number_theory_91558 :
    ∃ n : ℕ, 0 < n ∧ (2009 * 2010 * 2011) ∣ (n ^ 6 + 31 * n ^ 4 - 900) := by
  use 1
  constructor
  · norm_num
  · norm_num