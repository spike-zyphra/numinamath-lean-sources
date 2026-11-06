import Mathlib

theorem number_theory_182560 {n : ℕ} (hn : n = 316990099009901) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p * q = n ∧ p < q := by 
  rw [hn]
  use 4002001, 79207901
  constructor
  · -- Show 4002001 is prime
    norm_num
  constructor
  · -- Show 79207901 is prime
    norm_num
  constructor
  · -- Show they are not equal
    norm_num
  constructor
  · -- Show their product is n
    all_goals norm_num
  · -- Show that the first is less than the second
    all_goals norm_num