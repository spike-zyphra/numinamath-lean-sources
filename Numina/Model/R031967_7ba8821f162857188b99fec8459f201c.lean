import Mathlib

theorem number_theory_234838 (a : ℤ) :
    IsCoprime (a^2 + 3) (a^4 + 7 * a^2 + 11) := by
  use a ^ 2 + 4
  use -1
  ring_nf