import Mathlib

theorem algebra_20278 {n : ℕ} (hn : n = 111111111) :
    IsLeast {x | x ≥ 100000000 ∧ ∃ k, x = k * 111111111} n := by 
  rw [hn]
  constructor
  · -- First, we need to prove 111111111 ∈ {x | x ≥ 100000000 ∧ ∃ k, x = k * 111111111}
    constructor
    · -- 111,111,111 ≥ 100,000,000
      norm_num
    · -- ∃ k, 111111111 = k * 111111111
      use 1
      all_goals norm_num
  · -- prove 111111111 is the smallest
    intro x hx
    rcases hx with ⟨hx1, h2⟩
    rcases h2 with ⟨k, hk⟩
    have h3 : k ≥ 1 := by
      by_contra h
      push_neg at h
      have h0 : k = 0 := by linarith
      rw [h0] at hk
      linarith
    nlinarith