import Mathlib

theorem number_theory_286620 {N : ℤ} (hN : N > 0) :
    ∃ p q u v : ℤ, N = p * q + u * v ∧ u - v = 2 * (p - q) := by
  use N
  use 1
  use 0
  use -2 * (N - 1)
  constructor
  · -- Check first equation
    ring
  · -- Check second equation
    ring