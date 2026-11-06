import Mathlib

theorem number_theory_323433 :
    ∃ n : ℕ, (Nat.digits 10 (n ^ 2)).sum = 2002 := by
  use 10 ^ 222 - 3
  native_decide