import Mathlib

/- Let $f(n)$ be the sum of the positive integer divisors of $n$. If $n$ is prime and $f(f(n))$ is also prime, then call $n$ a bouncy prime. What is the smallest bouncy prime? -/
theorem number_theory_19486 :
    IsLeast {n | Nat.Prime n ∧ Nat.Prime (∑ d in (∑ d in n.divisors, d).divisors, d)} 3 := by
  simp [IsLeast, lowerBounds]
  -- Break the goal into two parts.
  refine ⟨?_, ?_⟩
  . -- Verify that 3 is a bouncy prime.
    simp [Nat.prime_three, show Nat.divisors 4 = {1, 2, 4} by native_decide] -- Use native_decide to show that the divisor set of 4 is {1, 2, 4}.
    native_decide -- Show that 7 is a prime.
  . intro n
    contrapose!
    intro h
    obtain ⟨h, h'⟩  := h
    interval_cases n
    . native_decide -- Show that 0 is not a prime.
    . native_decide -- Show that 1 is not a prime.
    . intro _
      simp [show Nat.divisors 2 = {1, 2} by native_decide, show Nat.divisors 3 = {1, 3} by native_decide] at h -- Use native_decide to show that the divisor set of 3 is {1, 3}.
      absurd h
      native_decide -- Show that 4 is not a prime.
  