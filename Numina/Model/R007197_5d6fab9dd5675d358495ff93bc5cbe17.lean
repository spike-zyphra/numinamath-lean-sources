import Mathlib

theorem number_theory_180655 (n : ℕ) (hn : n > 0) :
    IsLeast {k | ∃ x y, x * 7 - y * 4 = 2024 ∧ k = x + y} 297 := by 
  constructor
  · -- Show 297 is achievable with x = 292, y = 5
    use 292, 5
    all_goals
      omega
  · -- Show no smaller k is achievable
    intro k hk
    rcases hk with ⟨x, y, h_eq, h_sum⟩
    -- We have x * 7 - y * 4 = 2024
    -- We have k = x + y
    -- We need to show that k >= 297
    omega