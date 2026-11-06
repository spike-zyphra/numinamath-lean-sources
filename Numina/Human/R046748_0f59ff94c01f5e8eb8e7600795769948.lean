import Mathlib

/- The greatest common divisor of two integers is $(x+3)$ and their least common multiple is $x(x+3)$, where $x$ is a positive integer. If one of the integers is 40, what is the smallest possible value of the other one? -/
theorem number_theory_23049 :
    IsLeast {b : ℕ | ∃ x : ℕ, x > 0 ∧ Nat.gcd 40 b = x + 3 ∧ Nat.lcm 40 b = x * (x + 3)} 8 := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . use 5
    norm_num
  . intro b x xpos h₁ h₂
    have h₃ := Nat.gcd_mul_lcm 40 b
    rw [h₁, h₂] at h₃
    have h₄ : x ≥ 5 := by
      by_contra! h₄
      -- We show that x = 1, 2, 3, 4 are not possible.
      interval_cases x
      all_goals
        omega -- Basically we determine that the LHS of h₃ is not divisible by 40.
    suffices h₅ : (x + 3) * (x * (x + 3)) ≥ 40 * 8 by
      rw [h₃] at h₅
      rw [ge_iff_le, mul_le_mul_left] at h₅
      exact h₅
      norm_num
    nlinarith