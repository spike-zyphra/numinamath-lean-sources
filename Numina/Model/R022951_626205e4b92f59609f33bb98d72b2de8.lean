import Mathlib

theorem number_theory_114648 :
    IsLeast {n | 28 ∣ n ∧ n % 15 = 4} 364 := by
  constructor
  · -- Show 364 is in the set
    constructor
    · -- Show 28 divides 364
      norm_num
    · -- Show 364 % 15 = 4
      norm_num
  · -- Show 364 is minimal in the set
    intro n hn
    rcases hn with ⟨h1, h2⟩
    omega