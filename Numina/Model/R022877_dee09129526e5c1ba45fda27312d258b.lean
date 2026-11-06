import Mathlib

theorem algebra_18715 :
    IsLeast {p : ℕ | p.Prime ∧ ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧ q + r = p} 5 := by

  constructor
  · -- Show that 5 is in the set.
    constructor
    · norm_num
    · -- Show existence of q and r
      use 2, 3
      all_goals norm_num
  · -- Show that 5 is indeed the smallest
    intro p hp
    rcases hp with ⟨h1, ⟨q, r, hq, hr, hneq, heq⟩⟩
    by_contra h
    push_neg at h
    have h2 : p < 5 := by linarith
    have h3 : q ≤ 4 := by
      omega
    have h4 : r ≤ 4 := by
      omega
    interval_cases q <;> interval_cases r 
      <;> norm_num at hq hr hneq heq 
      <;> norm_num [heq] at h1 
      <;> omega