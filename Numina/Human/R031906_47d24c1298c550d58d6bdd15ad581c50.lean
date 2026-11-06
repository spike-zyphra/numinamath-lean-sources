import Mathlib
/- Compute the smallest integer $n>72$ that has the same set of prime divisors as 72 . -/
theorem number_theory_610784 : IsLeast {n : ℕ | n > 72 ∧ Nat.primeFactors n = Nat.primeFactors 72} 96:= by
  -- We need to prove two things: 1) 96 is in the set, and 2) 96 is the smallest element in the set.
  constructor
  -- First, we prove that 96 is in the set, i.e., 96 > 72 and Nat.primeFactors 96 = Nat.primeFactors 72.
  .
    simp
    native_decide
  -- Second, we prove that 96 is the smallest element in the set.
  .
    simp [lowerBounds]
    -- For any n in the set, we need to show that n ≥ 96.
    intro n hn h
    -- We prove by contradiction.
    by_contra H
    simp at H
    -- We consider all possible values of n between 73 and 95.
    interval_cases n
    -- For each case, we show that n cannot have the same prime factors as 72.
    all_goals
      absurd h
      native_decide
