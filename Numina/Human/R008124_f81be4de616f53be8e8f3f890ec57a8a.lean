import Mathlib

/- An abundant number is a positive integer such that the sum of its proper divisors is greater than the number itself. The number 12 is an abundant number since $1 + 2 + 3 + 4 + 6 > 12$. What is the smallest abundant number that is not a multiple of 6? -/
theorem number_theory_14834
    (is_abundant : ℕ → Prop)
    (def_is_abundant : ∀ n, is_abundant n = (∑ d in n.properDivisors, d > n)) :
    IsLeast {n | is_abundant n ∧ ¬6 ∣ n} 20 := by

  -- For any prime number, the sum of its proper divisors is equal to $1$, so a prime number cannot be an abundant number.
  have (n : ℕ) : n.Prime → ¬ is_abundant n := by
    intro hnp
    rw [def_is_abundant, gt_iff_lt, not_lt, ← n.pow_one, Nat.properDivisors_prime_pow hnp 1]
    simp [Nat.Prime.one_le hnp]

  simp only [def_is_abundant, IsLeast]
  constructor
  . native_decide
  . simp [lowerBounds]
    intro a ha1 ha2
    rcases Nat.lt_or_ge a 20
    . interval_cases a
      -- Therefore, it suffices to check the smallest composite numbers that are not divisible by $6$. Thus, the answer is $\boxed{20}$.
      any_goals norm_num at ha1 ha2
      -- for $4$, $1 + 2 < 4$,
      . simp [show Nat.properDivisors 4 = {1, 2} by decide] at ha1
      -- for $8$, $1 + 2 + 4 < 8$,
      . simp [show Nat.properDivisors 8 = {1, 2, 4} by decide] at ha1
      -- for $9$, $1 + 3 < 9$,
      . simp [show Nat.properDivisors 9 = {1, 3} by decide] at ha1
      -- for $10$, $1 + 2 + 5 < 10$,
      . simp [show Nat.properDivisors 10 = {1, 2, 5} by decide] at ha1
      -- for $14$, $1 + 2 + 7< 14$,
      . simp [show Nat.properDivisors 14 = {1, 2, 7} by decide] at ha1
      -- for $15$, $1 + 3 + 5< 15$,
      . simp [show Nat.properDivisors 15 = {1, 3, 5} by decide] at ha1
      -- for $16$, $1 + 2 + 4 + 8 < 16$,
      . simp [show Nat.properDivisors 16 = {1, 2, 4, 8} by decide] at ha1
    . linarith
