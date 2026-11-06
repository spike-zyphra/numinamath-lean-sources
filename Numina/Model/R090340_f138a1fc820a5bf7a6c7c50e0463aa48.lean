import Mathlib

theorem number_theory_77547 :
    IsLeast {p | p.Prime ∧ ∃ k, (Nat.digits 10 p).sum = k ∧ k.Prime ∧ k > 10} 29 := by
  constructor
  · -- Let's prove 29 is in our set
    constructor
    · -- 29 is prime
      norm_num
    · -- Let's take k = 11 and verify the conditions
      use 11
      constructor
      · -- Verify that the digits of 29 (which are [2, 9]) sum to 11
        norm_num
      constructor
      · -- 11 is prime
        norm_num
      · -- 11 > 10
        norm_num
  · -- Now, prove that 29 is the smallest such prime
    intro p hp
    rcases hp with ⟨prime_p, ⟨k, rfl, prime_k, hk⟩⟩
    by_contra! h
    interval_cases p <;> norm_num at prime_p ⊢ <;> norm_num at *
    <;> contradiction