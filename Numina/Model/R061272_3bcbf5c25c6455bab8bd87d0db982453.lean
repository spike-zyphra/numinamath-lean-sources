import Mathlib

theorem number_theory_13428 :
    IsLeast {x : ℕ | 0 < x ∧ ∃ k : ℕ, 0 < k ∧ k^2 = x^2 + 2021} 2 := by 
  constructor
  · -- Show that 2 is in the set
    constructor
    · norm_num -- Show that 2 is positive
    · use 45
      all_goals norm_num -- Verify that 45 is positive and 45^2 = 2^2 + 2021
  · -- Show that 2 is the smallest element in the set
    intro x
    intro hx
    rcases hx with ⟨hx_pos, k, hk_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : x = 1 := by
      interval_cases x <;> omega
    rw [h1] at h_eq
    have h2 : k < 45 := by 
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg ((k : ℕ) : ℕ)]
    interval_cases k <;> omega