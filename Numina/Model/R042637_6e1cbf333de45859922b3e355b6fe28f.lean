import Mathlib

theorem number_theory_204061 (n : ℤ) (hn : n > 5) :
    ∃ a b c, a^2 + b^2 + c^2 = 3 * (n - 1)^2 + 32 := by 
  use n - 1
  use n - 5
  use n + 3
  ring_nf