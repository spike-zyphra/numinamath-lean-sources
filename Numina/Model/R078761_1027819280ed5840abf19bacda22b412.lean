import Mathlib

theorem number_theory_280039 : IsLeast {n | n % 2 = 1 ∧ n % 3 = 2} 5 := by 
  constructor 
  · -- First, we show that 5 belongs to the set {n | n % 2 = 1 ∧ n % 3 = 2}.
    show 5 % 2 = 1 ∧ 5 % 3 = 2
    constructor 
    · norm_num 
    · norm_num 
  · -- Now, we show that 5 is the smallest element in the set.
    intro n hn 
    rcases hn with ⟨h1, h2⟩ 
    omega