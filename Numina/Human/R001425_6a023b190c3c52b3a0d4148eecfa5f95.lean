import Mathlib

/-6. (NET 1) Find four positive integers each not exceeding 70000 and each having more than 100 divisors. -/
theorem number_theory_24044 : ∃ a b c d : ℕ, a < b ∧ b < c ∧ c < d ∧ d ≤ 70000 ∧ a.divisors.card > 100 ∧ b.divisors.card > 100 ∧ c.divisors.card > 100 ∧ d.divisors.card > 100 := by
  -- We choose the following four numbers:
  -- 50400 = 2^5 × 3^2 × 5^2 × 7
  use 50400
  -- 55440 = 2^4 × 3^2 × 5 × 7 × 11
  use 55440
  -- 60480 = 2^5 × 3^3 × 5 × 7
  use 60480
  -- 65520 = 2^4 × 3^2 × 5 × 7 × 13
  use 65520
  -- Simplify the goal, to eliminate order cases
  simp
  refine ⟨?_, ?_, ?_, ?_⟩  
  . -- Prove that 50400 has over 100 divisors
    native_decide
  . -- Prove that 55440 has over 100 divisors
    native_decide
  . -- Prove that 60480 has over 100 divisors
    native_decide
  . -- Prove that 65520 has over 100 divisors
    native_decide
  