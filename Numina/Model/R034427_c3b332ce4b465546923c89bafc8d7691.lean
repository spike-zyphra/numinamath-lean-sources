import Mathlib

theorem number_theory_77447 {n : ℕ} (hn : n = 400000001) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p * q = n ∧ p = 20201 ∧ q = 19801 := by 
  use 20201, 19801
  constructor
  · -- Show p is prime
    norm_num
  constructor
  · -- Show q is prime
    norm_num
  constructor
  · -- Show p * q = n
    rw [hn]
    all_goals norm_num
  constructor
  · -- Show p = 20201
    rfl
  · -- Show q = 19801
    rfl