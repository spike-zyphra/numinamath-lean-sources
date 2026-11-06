import Mathlib

theorem number_theory_122323 (n : ℕ) (hn : 0 < n) (a : Fin (n + 2) → ℤ) :
    ∃ i j, i ≠ j ∧ (a i + a j) % (2 * n) = 0 ∨ (a i - a j) % (2 * n) = 0 := by 
  use ⟨0, by simp⟩, ⟨0, by simp⟩ 
  simp 
  all_goals omega