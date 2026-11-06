import Mathlib

/- What is the smallest positive integer $x$ for which $x^{2}+x+41$ is not a prime?-/
theorem number_theory_610937 :
    IsLeast {x : ℕ | 0 < x ∧ ¬Nat.Prime (x ^ 2 + x + 41)} 40 := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  .  -- Prove that 40 is in the set, because 40² + 40 + 41 = 41 * 41.
    rw [show 1681 = 41 * 41 by norm_num]
    apply Nat.not_prime_mul (by norm_num) (by norm_num)
  . -- Prove that all smaller numbers give primes.
    -- The only way is to enumerate.
    intro x hx
    contrapose!
    intro hx'
    interval_cases x
    all_goals
      native_decide
