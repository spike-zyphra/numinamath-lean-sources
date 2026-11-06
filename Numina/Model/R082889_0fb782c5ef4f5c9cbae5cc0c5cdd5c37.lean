import Mathlib

theorem number_theory_15240 (n : ℕ) (h₀ : n > 30) (h₁ : ∃ k, n = 3 * k + k + 1) :
    IsLeast {x | x > 30 ∧ ∃ k, x = 3 * k + k + 1} 33 := by
  constructor
  · -- First, we show 33 is in this set
    constructor
    · norm_num
    · use 8
      all_goals norm_num
  · -- Now, we need to prove that 33 is the smallest
    intro m hm
    rcases hm with ⟨hm1, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h2 : m ≤ 32 := by omega
    have h3 : m > 30 := hm1
    have h4 : m = 31 ∨ m = 32 := by omega
    rcases h4 with (h5 | h5)
    · -- If m = 31
      rw [h5] at hk
      omega -- Derive contradiction from equality
    · -- If m = 32
      rw [h5] at hk
      omega -- Derive contradiction from equality