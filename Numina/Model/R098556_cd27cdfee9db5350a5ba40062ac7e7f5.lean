import Mathlib

theorem number_theory_217494 : ∃ a b c : ℕ, a^3 + b^4 = c^5 := by
  use 256, 64, 32
  norm_num