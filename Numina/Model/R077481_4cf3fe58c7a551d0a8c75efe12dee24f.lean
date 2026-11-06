import Mathlib

theorem number_theory_7483 : ∑ n in (Finset.Icc 10 99), (Nat.digits 10 n).prod = 2025 := by
  native_decide