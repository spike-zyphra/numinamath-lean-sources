import Mathlib

theorem number_theory_256060 (n : ℤ) : IsCoprime n (n + 1) := by
  show IsCoprime n (n + 1)
  use -1, 1
  ring_nf
  <;> omega