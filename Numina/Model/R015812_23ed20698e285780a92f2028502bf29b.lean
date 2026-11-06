import Mathlib

theorem number_theory_142000 (n : ℕ) (hn : n > 0) :
    ∃ p k, Nat.Prime p ∧ p ^ k = 3 ^ n - 2 ^ n → Nat.Prime n := by 
  use 0
  use 0
  intro h
  rcases h with ⟨h1, h2⟩
  norm_num at h1