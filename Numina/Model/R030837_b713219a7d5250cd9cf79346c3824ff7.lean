import Mathlib

theorem number_theory_114422 (m n : ℕ) (hmn : m ≠ n) :
    ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = m^4 + 4 * n^4 := by 
  use m^2
  use 0
  use 0
  use 2 * n^2
  all_goals
  ring_nf