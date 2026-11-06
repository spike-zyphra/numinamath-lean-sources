import Mathlib

theorem number_theory_101929 (n : ℤ) : ∃ k, k^2 = n * (n + 1) ↔ n = 0 ∨ n = -1 := by 
  use 0
  constructor
  · -- Forward: If 0^2 = n * (n + 1), prove n = 0 or n = -1
    intro h
    have h1 : n * (n + 1) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case h2: n = 0
      left
      exact h2
    · -- Case h3: n + 1 = 0
      right
      linarith
  · -- Backward: If n = 0 or n = -1, then 0^2 = n * (n + 1)
    rintro (h | h)
    · -- Case n = 0
      rw [h]
      all_goals norm_num
    · -- Case n = -1
      rw [h]
      all_goals norm_num