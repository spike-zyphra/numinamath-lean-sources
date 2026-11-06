import Mathlib

theorem number_theory_105795 :
    IsLeast {n | n % 4 = 2 ∧ n % 5 = 3 ∧ n % 6 = 4 ∧ n % 12 = 10} 58 := by
  constructor
  · -- Show that 58 is in the set
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that 58 is the smallest
    intro n hn
    have h1 : n % 4 = 2 := hn.1
    have h2 : n % 5 = 3 := hn.2.1
    have h3 : n % 6 = 4 := hn.2.2.1
    have h4 : n % 12 = 10 := hn.2.2.2
    by_contra h
    push_neg at h
    omega