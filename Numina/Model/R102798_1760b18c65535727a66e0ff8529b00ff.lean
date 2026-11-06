import Mathlib

theorem number_theory_94293 : (Nat.digits 10 (Nat.sqrt (25^64 * 64^25))).sum = 14 := by
  native_decide