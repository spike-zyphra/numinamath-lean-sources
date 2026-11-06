import Mathlib

theorem number_theory_319686 (N : ℤ) (hN : N > 0) :
    ∃ p q u v : ℤ, N = p * q + u * v ∧ u - v = 2 * (p - q) := by
  use N
  use 1
  use 0
  use -2 * (N - 1)
  constructor
  · -- Show that N = p * q + u * v
    ring
  · -- Show that u - v = 2 * (p - q)
    ring