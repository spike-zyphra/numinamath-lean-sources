import Mathlib

/- Prove that there exists a prime number  $p$ , such that the sum of digits of  $p$  is a composite odd integer. Find the smallest such  $p$ .-/
theorem number_theory_8521 :
    IsLeast {p : ℕ | p.Prime ∧ Odd (Nat.digits 10 p).sum ∧ ¬(Nat.digits 10 p).sum.Prime} 997 := by
  -- Assume that there is a prime number less than 997 and satisfies above condition.
  by_contra h
  simp [IsLeast] at h
  specialize h (by norm_num) (by use 12; norm_num) (by norm_num)
  simp [lowerBounds] at h
  contrapose! h
  intro x hx dsum_odd dsum_not_prime
  by_contra! h
  -- Check all the prime number less than 997, we did not find such prime number.
  -- Hence the result holds true.
  interval_cases x <;> norm_num at hx <;> norm_num at dsum_not_prime
  all_goals rw [Nat.odd_iff] at dsum_odd; norm_num at dsum_odd
