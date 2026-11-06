import Mathlib

theorem number_theory_3676 : ∃r : Finset ℕ, r = {b : ℕ | b ∈ Set.Icc 100 999 ∧ Nat.gcd (Nat.gcd b 1112) b = 139} ∧ r.sum id = 2224 := by 
  use {139, 417, 695, 973}
  constructor 
  · -- Show the first part of the conjunction, i.e., r = {b | b ∈ Set.Icc 100 999 ∧ ...}
    ext b
    simp [Finset.mem_insert, Finset.mem_singleton, Set.mem_setOf_eq]
    constructor 
    · -- Show the forward direction of the iff 
      intro h 
      rcases h with (rfl | rfl | rfl | rfl)
      all_goals
        constructor 
        · -- Show that it's in the range 
          norm_num 
        · -- Show that gcd equals 
          norm_num 
    · -- Show the backward direction of the iff 
      intro h 
      simp at h 
      obtain ⟨⟨h3, h4⟩, h7⟩ := h 
      interval_cases b <;> norm_num [Nat.gcd] at h7 h3 h4 ⊢ <;> 
        try { contradiction } 
  · -- Show the sum is correct 
    native_decide