import Mathlib

theorem number_theory_122677 (n : ℤ) :
    IsCoprime (2*n^2+9*n-17) (n+6) := by
  show IsCoprime (2 * n ^ 2 + 9 * n - 17) (n + 6)
  use 1, -2 * n + 3
  ring_nf
  <;> omega