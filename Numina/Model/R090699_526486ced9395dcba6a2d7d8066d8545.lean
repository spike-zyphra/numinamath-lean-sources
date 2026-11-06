import Mathlib

theorem number_theory_264778 :
    IsLeast {n | (n % 10000 = 2018) ∧ 2017 ∣ n} 8782018 := by
  constructor
  · -- Verify that 8782018 is in the set
    constructor
    · -- Show that 8782018 % 10000 = 2018
      norm_num
    · -- Show that 2017 divides 8782018
      norm_num
  · -- Show that 8782018 is the smallest element in the set
    intro m hm
    rcases hm with ⟨hm1, hm2⟩
    omega