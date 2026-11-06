import Mathlib

theorem number_theory_233597 : ∃ (p q r : ℕ), p.Prime ∧ q.Prime ∧ r.Prime ∧ p*q*r=3*(p+q+r) := by
  use 2, 3, 5
  constructor
  · -- Show 2 is prime
    norm_num
  constructor
  · -- Show 3 is prime
    norm_num
  constructor
  · -- Show 5 is prime
    norm_num
  · -- Verify the equation
    all_goals norm_num