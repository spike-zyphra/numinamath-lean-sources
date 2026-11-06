import Mathlib

/-
Proves that for any natural numbers x and a with a ≥ 1 and x coprime to a,
there exists a natural number b ≥ 1 such that x^b ≡ 1 mod a.
This is a fundamental result in number theory related to modular arithmetic.
-/
theorem Number_Theory_638849
    {x a : ℕ}
    (ha : a ≥ 1)
    (h_coprime : x.Coprime a) :
    ∃ b : ℕ, b ≥ 1 ∧ a ∣ x ^ b - 1 := by

  -- Use case analysis to handle trivial and non-trivial cases separately
  by_cases H: a = 1

  · -- Case 1: If a = 1, then any b works since 1 divides any number.
    use 1

    -- Simplify the expression using the fact that a = 1.
    simp[H]

  · -- Case 2: If a > 1, use Euler's theorem on modular arithmetic.
    push_neg at H

    -- Use omega tactic to derive a > 1 from a ≥ 1 and a ≠ 1.
    have ha: a > 1 := by omega

    -- Use Euler's totient function φ(a) as the exponent b.
    use a.totient

    -- Split the goal into two subgoals: b ≥ 1 and a∣x^b - 1.
    split_ands

    · -- Prove that φ(a) ≥ 1 when a > 1.
      refine Nat.add_one_le_iff.mpr ?_

      -- Use the fact that the totient function is positive for a > 1.
      have ha : 0 < a := by omega
      exact Nat.totient_pos.mpr ha

    · -- Prove that a divides x^φ(a) - 1 using modular arithmetic.
      refine (Nat.modEq_iff_dvd' ?_).mp ?_

      -- Prove that x^φ(a) ≥ 1 to ensure the modular arithmetic is well-defined.
      refine Nat.one_le_pow a.totient x ?_

      -- Prove that x ≠ 0 to apply the power lemma.
      refine Nat.zero_lt_of_ne_zero ?_

      -- Assume x = 0 for contradiction.
      by_contra w

      -- Simplify the coprimality condition using x = 0.
      simp[w] at h_coprime

      -- Derive a contradiction from the simplified coprimality condition.
      omega

      -- Apply Euler's theorem: x^φ(a) ≡ 1 mod a when x and a are coprime.
      exact Nat.ModEq.symm (Nat.ModEq.pow_totient h_coprime)
