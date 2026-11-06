import Mathlib

theorem number_theory_211487 (N : ℕ) :
    (Nat.digits 10 N).sum - (Nat.digits 10 (5^5 * N)).sum ≤ 5 * (Nat.digits 10 N).sum := by 
  omega