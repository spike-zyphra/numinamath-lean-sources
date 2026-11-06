import Mathlib

theorem number_theory_90227 (n : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n ∣ p - q := by
  use 2, 3
  constructor
  · -- Show that 2 is prime
    norm_num
  constructor
  · -- Show that 3 is prime
    norm_num
  constructor
  · -- Show that 2 ≠ 3
    norm_num
  · -- Show that n divides (2 - 3)
    simp
    all_goals try { 
      omega 
    }