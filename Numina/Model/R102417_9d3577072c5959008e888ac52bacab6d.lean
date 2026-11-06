import Mathlib

theorem algebra_13605 :
    IsLeast {k : ℕ | 0 < k ∧ ∃ x : ℝ, (k - 3) * x ^ 2 + (k - 2) * x - 1 = 0} 3 := by 
  constructor
  · -- Show 3 is in the set
    constructor
    · norm_num
    · -- Show existence of a real root when k = 3
      use 1
      norm_num
  · -- Show that 3 is the smallest
    intro k hk
    rcases hk with ⟨hk_pos, ⟨x, hx⟩⟩
    by_contra h
    push_neg at h
    have h1 : k = 1 ∨ k = 2 := by
      have h2 : k < 3 := by linarith
      interval_cases k <;> tauto
    rcases h1 with (rfl | rfl)
    · -- Case k = 1: Show contradiction
      norm_num at hx
      nlinarith [sq_nonneg (x + 1 / 4 : ℝ), sq_nonneg (x : ℝ)]
    · -- Case k = 2: Show contradiction
      norm_num at hx
      nlinarith [sq_nonneg (x : ℝ)]