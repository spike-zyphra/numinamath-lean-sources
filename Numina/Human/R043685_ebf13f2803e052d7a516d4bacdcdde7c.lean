import Mathlib

/- What is the greatest three-digit number "abc'' such that $4,a,b$ forms a geometric sequence and $b,c,5$ forms an arithmetic sequence? -/
theorem algebra_20965 :
    IsGreatest {x | ∃ a b c : ℤ, 100 * a + 10 * b + c = x ∧ 1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧ ∃ r : ℚ, a = 4 * r ∧ b = a * r ∧ ∃ d, c = b + d ∧ 5 = c + d} 697 := by
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- Prove that the maximum could be attained.
    use 6, 9, 7
    norm_num
    use 3 / 2
    norm_num
    use -2
    norm_num
  . -- Prove that every number satisfying the condition is less than or equal to 697.
    intro x a b c hx ha₀ _ hb₀ hb₁ hc₀ hc₁ r h₀ h₁ d h₂ h₃
    rw [h₂] at h₃
    rw [h₀] at h₁
    -- Since b is at most 9, a is at most 6.
    replace ha₁ : a ≤ 6 := by
      qify at hb₁ ⊢
      rw [h₁, show 4 * r * r = (2 * r) ^ 2 by ring_nf, show (9 : ℚ) = 3 ^ 2 by norm_num] at hb₁
      simp [sq_le_sq, abs] at hb₁
      linarith only [hb₁.1, h₀]
    by_cases hc₀ : c ≤ 7
    . -- If c ≤ 7, we are done.
      omega
    . -- If c > 7, then the resulting three-digit number x must be smaller than 697.
      simp at hc₀
      interval_cases c
      all_goals
        omega -- Obtain a contradiction from h₃, h₂ and hb₁.
