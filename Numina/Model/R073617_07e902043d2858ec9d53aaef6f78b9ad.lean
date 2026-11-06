import Mathlib

theorem number_theory_52989 : (Nat.digits 10 (2^29)).length = 9 ∧
    (Nat.digits 10 (2^29)).toFinset = Finset.Icc 0 9 \ {4} := by
  native_decide