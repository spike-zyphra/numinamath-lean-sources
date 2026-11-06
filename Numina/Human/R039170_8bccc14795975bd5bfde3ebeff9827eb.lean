import Mathlib

/- 1. Let $a$ and $b$ be positive integers, $1176a = b^4$. Find the minimum value of $a$.-/
theorem number_theory_302345 :
    IsLeast {a : ℕ | 0 < a ∧ ∃ b, 0 < b ∧ 1176 * a = b ^ 4} 2646 := by
  -- Simplify the goal in two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- First show that there is some b such that the value a = 2646 is possible.
    use 42
    norm_num
  . -- Now show that given the conditions we must have a ≥ 2646.
    intro a ha b hb h
    -- Assume on the contrary that a < 2646.
    by_contra h'
    push_neg at h'
    -- We have b < 42.
    have h₀ : b ^ 4 < 42 ^ 4 := by
      nlinarith
    rw [Nat.pow_lt_pow_iff_left (by norm_num)] at h₀
    -- Try each possible case of b and see that the hypothesis 1176a = b⁴ cannot hold.
    interval_cases b
    <;> omega