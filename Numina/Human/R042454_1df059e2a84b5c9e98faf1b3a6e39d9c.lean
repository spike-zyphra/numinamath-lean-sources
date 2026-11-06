import Mathlib

theorem number_theory_144333 :
    IsLeast {x | ∃ n, x = 15 * n + 2 ∧ ∃ m, x = 28 * m + 8} 92 := by 
  constructor
  · use 6
    constructor
    · rfl
    · use 3
  · intro x hx
    rcases hx with ⟨n, hn1, m, hn2⟩
    omega