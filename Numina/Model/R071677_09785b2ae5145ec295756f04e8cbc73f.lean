import Mathlib

theorem number_theory_104782 : (Nat.factorial 30) % 10^7 = 0 ∧ ¬(Nat.factorial 30) % 10^8 = 0 := by
  native_decide