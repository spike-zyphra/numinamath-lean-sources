import Mathlib

/- Suppose $a$ and $b$ are positive integers such that $a^{b}=2^{2023}$. Compute the smallest possible value of $b^{a}$.-/
theorem number_theory_610576 :
    IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ b = 2 ^ 2023 ∧ n = b ^ a} 1 := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- First show that bᵃ = 1 is possible.
    use 2 ^ 2023, by positivity, 1, by norm_num
    simp
  . -- Then show that it is the smallest possible value.
    intro n a h₁ b h₂ h₃ h₄
    clear h₃
    rw [h₄, show 1 = b ^ 0 by simp]
    apply Nat.pow_le_pow_right h₂ (le_of_lt h₁)
