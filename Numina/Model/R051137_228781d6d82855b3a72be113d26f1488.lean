import Mathlib

theorem number_theory_12144 (n : ℤ) (hn : n > 0) :
    IsCoprime (3 * n + 1) (5 * n + 2) := by 
  show IsCoprime (3 * n + 1) (5 * n + 2)
  use -5, 3
  ring_nf
  <;> omega