import Mathlib

theorem number_theory_301314 (S : Set ℕ) (hS : S = {11, 13}) :
    ¬∃ n, n ∈ S ∧ n = 119 ∧
    ∀ m > 119, ∃ k, m ∈ S ∧ k > 0 ∧ m - k ∈ S := by 
  rintro ⟨n, hn1, hn2, hn3⟩
  rw [hS] at hn1
  simp at hn1 
  all_goals 
    omega