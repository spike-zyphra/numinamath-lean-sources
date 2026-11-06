import Mathlib

/- 3. There exists an integer $n$ such that $\sqrt{p+n}+\sqrt{n}$ is an integer for the prime number $p$
(A) does not exist;
(B) there is only one;
(C) there are more than one, but a finite number;
(D) there are infinitely many. -/
theorem number_theory_276901 :
    {p : ℕ | p.Prime ∧ ∃ n : ℤ, ∃ k : ℤ, √ (p + n) + √ n = k}.Infinite := by
  -- we will prove the set of odd primes are subset of the set, the set of odd primes is infinite, so this set is infinite
  apply Set.Infinite.mono (s := {p : ℕ | p.Prime ∧ p ≠ 2})
  . simp
    rintro p hp hp2
    and_intros
    . exact hp
    . replace hp2 : Odd p := by exact Nat.Prime.odd_of_ne_two hp hp2
      -- odd prime can be written as 2 * x + 1
      obtain ⟨x, hx⟩ := hp2
      -- then such n is x^2 and k is 2 * x + 1
      use x^2, 2 * x + 1
      rw [hx]
      push_cast
      -- write the terms under square root as squares
      convert_to √((x + 1)^2) + √(x^2) = 2 * x + 1
      . ring_nf
      rw [Real.sqrt_sq (by positivity)]
      rw [Real.sqrt_sq (by positivity)]
      ring
  -- set of odd primes is infinite as that is just set of primes - {2}, set of primes is infinite and {2} is finite
  . convert_to ({p | Nat.Prime p} \ {2}).Infinite
    apply Set.Infinite.diff
    . exact Nat.infinite_setOf_prime
    . simp