import Mathlib

theorem number_theory_111292 (n : ℤ) : IsCoprime (21*n+4) (14*n+3) := by
  use -2
  use 3
  ring_nf
  <;> omega