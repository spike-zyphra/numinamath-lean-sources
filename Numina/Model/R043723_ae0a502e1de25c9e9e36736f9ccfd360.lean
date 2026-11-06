import Mathlib

def is_useful (n : ℕ) : Prop :=
  (Nat.digits 10 n).all (fun d => d ≠ 0) ∧
  (Nat.digits 10 n).length = 3 ∧
  (Nat.digits 10 n).toFinset.card = 3 ∧
  (Nat.digits 10 n).prod % (Nat.digits 10 n).sum = 0

theorem number_theory_284746 :
    ∃ n, is_useful n ∧ is_useful (n + 1) := by 
  use 578
  constructor
  · -- Show 578 is useful
    constructor
    · -- Show that all digits are non-zero
      native_decide
    constructor
    · -- Show that the length of digits is 3
      native_decide
    constructor
    · -- Show that the cardinality of the Finset of digits is 3
      native_decide
    · -- Show that product modulo sum is zero
      native_decide
  · -- Show 579 is useful
    constructor
    · -- Show that all digits are non-zero
      native_decide
    constructor
    · -- Show that the length of digits is 3
      native_decide
    constructor
    · -- Show that the cardinality of the Finset of digits is 3
      native_decide
    · -- Show that product modulo sum is zero
      native_decide