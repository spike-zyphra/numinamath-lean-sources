import Mathlib

theorem number_theory_6658 :
    IsLeast {n | n % 5 = 3 ∧ n % 6 = 4 ∧ n % 7 = 5} 208 := by
  constructor
  · -- Show 208 is in the set
    show (208 : ℕ) % 5 = 3 ∧ (208 : ℕ) % 6 = 4 ∧ (208 : ℕ) % 7 = 5
    norm_num
  · -- Show no smaller positive integer is in the set
    intro n hn
    rcases hn with ⟨h1, h2, h3⟩
    by_contra h
    push_neg at h
    interval_cases n <;> omega