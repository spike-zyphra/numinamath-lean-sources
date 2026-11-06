import Mathlib

theorem number_theory_31454 (p : ℕ) (hp : Nat.Prime p) (h : 5 < p) :
    ∃ q n, Nat.Prime q ∧ q < p ∧ p ∣ n ^ 2 - q ∧ 0 < n := by 
  use 2
  use 1
  constructor
  · -- Show that 2 is prime
    norm_num
  constructor
  · -- Show that 2 < p
    linarith 
  constructor
  · -- Show that p divides 1^2 - 2
    norm_num 
    all_goals omega
  · -- Show that 0 < 1
    norm_num