import Mathlib

theorem number_theory_246394 : ∃ k, k ≤ (Nat.digits 10 (2^100)).length ∧ (Nat.digits 10 (2^100)).length ≤ k + 5 := by
  use 29
  constructor
  · -- Show 29 ≤ (Nat.digits 10 (2^100)).length
    native_decide
  · -- Show (Nat.digits 10 (2^100)).length ≤ 29 + 5
    native_decide