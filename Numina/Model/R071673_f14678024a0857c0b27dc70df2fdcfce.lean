import Mathlib

theorem number_theory_13833 :
  IsLeast {n | 0 < n ∧ 77 ∣ n ∧ (n % 10000) = 2020} 482020 := by
  constructor
  · -- Verify that 482020 is in the set.
    constructor
    · -- Show that 482020 is positive
      norm_num
    constructor
    · -- Show that 482020 is divisible by 77
      norm_num
    · -- Show that the last four digits of 482020 are 2020
      norm_num
  · -- Now show that 482020 is the smallest such number
    intro n hn
    rcases hn with ⟨hnpos, hndiv77, hnn2020⟩
    omega