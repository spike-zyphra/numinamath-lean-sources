import Mathlib

theorem number_theory_47432 :
    IsLeast {p : ℕ | p.Prime ∧ Odd (Nat.digits 10 p).sum ∧ ¬(Nat.digits 10 p).sum.Prime} 997 := by
  constructor
  · -- Verify that 997 is in the set
    constructor
    · -- Check that 997 is prime
      norm_num
    constructor
    · -- Check that the sum of digits of 997 is odd
      native_decide
    · -- Check that the sum of digits of 997 is not prime
      native_decide
  · -- Show 997 is minimal
    intro p hp
    rcases hp with ⟨h_prime, h_odd, h_not_prime⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h_prime h_odd h_not_prime <;> contradiction