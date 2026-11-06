import Mathlib

theorem algebra_275736 (n : ℕ) : ∃ m, m^2 = n * (n + 1) * (n + 2) * (n + 3) + 1 := by 
  use n^2 + 3 * n + 1
  ring_nf