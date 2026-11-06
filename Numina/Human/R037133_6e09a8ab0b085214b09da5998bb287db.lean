import Mathlib

open Nat

/- Find the least odd prime factor of $2019^8+1$. -/
theorem number_theory_97759 : IsLeast {p | Odd p ∧ Prime p ∧ p ∣ 2019^8 + 1} 97 := by
  -- Prove 97 divides 2019^8 + 1
  constructor
  · dsimp
    -- Prove 97 is odd
    constructor
    · use 48; norm_num
    -- Prove 97 is prime
    constructor
    · apply prime_def_lt'.mpr
      constructor
      · linarith
      · intro m hm hm' hdiv
        interval_cases m
        all_goals
          contrapose! hdiv
          norm_num
    norm_num
  rw [lowerBounds]
  dsimp
  rintro a ⟨odd_a, prime_a, ha⟩
  contrapose! ha
  have : 2 <= a := (prime_def_lt.mp prime_a).1
  -- Check that no other number less than 97 works
  interval_cases a
  all_goals
    norm_num
  contrapose! odd_a
  rw [not_odd_iff_even];
  norm_num