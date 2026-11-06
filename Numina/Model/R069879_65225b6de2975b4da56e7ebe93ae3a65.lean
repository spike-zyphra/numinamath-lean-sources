import Mathlib

theorem algebra_148217 : (Nat.digits 10 ((100^40 : ℕ) - 100^30 + 100^20 - 100^10 + 1)).sum = 361 := by
  native_decide