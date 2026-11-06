import Mathlib

theorem number_theory_164169 :
    ∃! n : ℕ, n ≠ 0 ∧ 100 % n = 4 ∧ 90 % n = 18 := by
  use 24
  constructor
  · -- Show that 24 is a solution
    constructor
    · -- Show that 24 ≠ 0
      norm_num
    constructor
    · -- Show that 100 % 24 = 4
      norm_num
    · -- Show that 90 % 24 = 18
      norm_num
  · -- Show that 24 is the unique solution
    intro n hn
    rcases hn with ⟨hnne0, h1, h2⟩
    have h3 : n ≤ 100 := by
      by_contra h
      push_neg at h
      have h4 : 100 % n = 100 := by
        rw [Nat.mod_eq_of_lt]
        all_goals
          omega
      omega
    have h4 : n ≤ 90 := by
      by_contra h
      push_neg at h
      have h5 : 90 % n = 90 := by
        rw [Nat.mod_eq_of_lt]
        all_goals
          omega
      omega
    interval_cases n <;> norm_num at h1 h2 hnne0 ⊢