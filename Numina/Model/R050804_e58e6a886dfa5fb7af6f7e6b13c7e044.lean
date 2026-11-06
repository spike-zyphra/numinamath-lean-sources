import Mathlib

theorem number_theory_147241 :
    ∃ n : ℕ, 2009 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d = 1 := by
  use 0
  constructor
  · -- Show that 2009 divides 0
    norm_num
  · -- Show that all digits of 0 are 1
    intro d hd
    simpa using hd