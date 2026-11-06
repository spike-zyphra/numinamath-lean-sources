import Mathlib

theorem number_theory_60239 :
    ∃ n : ℕ, (Nat.factorial n) % 10^1993 = 0 ∧ ¬(Nat.factorial n) % 10^1994 = 0 := by
  use 7985
  native_decide