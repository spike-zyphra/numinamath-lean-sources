import Mathlib

theorem number_theory_180655 (n : ℕ) (hn : n > 0) :
    IsLeast {k | ∃ x y, x * 7 - y * 4 = 2024 ∧ k = x + y} 297 := by 
  constructor
  · -- First, we show that 297 is achievable with x = 292 and y = 5
    use 292, 5
    repeat { constructor }
    all_goals norm_num
  · -- Now, we need to prove that 297 is minimal
    intro k h
    rcases h with ⟨x, y, h_eq, hk⟩
    omega