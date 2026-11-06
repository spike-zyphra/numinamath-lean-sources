import Mathlib

def is_perfect (n : ℕ) := n.divisors.sum id = 2 * n

theorem number_theory_256649 : ∃ p, is_perfect (16 * p) := by 
  use 31
  unfold is_perfect
  native_decide