import Mathlib

/- What is the smallest positive odd integer having the same number of positive divisors as 360 ? -/
theorem number_theory_605096 : IsLeast {n : ℕ | Odd n ∧ n.divisors.card = (Nat.divisors 360).card} 3465 := by
  -- 360 = 2^3 * 3^2 * 5
  -- So it has 24 divisors
  rw [show (Nat.divisors 360).card = 24 by native_decide]
  constructor
  . -- 3465 = 3^2 * 5 * 7 * 11, it has 24 divisors
    native_decide
  . -- We can check that any odd number < 3465 has less than 24 divisors
    intro n hn
    simp at hn
    contrapose! hn
    revert n
    native_decide