import Mathlib

/- Let $\alpha$ and $\beta$ be positive integers such that

$$
\frac{43}{197}<\frac{\alpha}{\beta}<\frac{17}{77}
$$

Find the minimum possible value of $\beta$. -/
theorem number_theory_607816:
    IsLeast {β : ℕ | 0 < β ∧ ∃ α : ℕ, 0 < α ∧ 43 / (197 : ℚ) < α / (β : ℚ) ∧ α / (β : ℚ) < 17 / (77 : ℚ)} 32 := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Show that β = 32 is possible by using α = 7.
    use 7
    norm_num
  . -- Show that β ≥ 32.
    intro β hβ α hα h₀ h₁
    -- Change the condition to 197 / 43 > β / α > 77 / 17.
    have h₂ : β / (α : ℚ) < 197 / (43 : ℚ) ∧ 77 / (17 : ℚ) < β / (α : ℚ) := by
      refine ⟨?_, ?_⟩
      all_goals
        rw [div_lt_div_iff₀] at h₀ h₁ ⊢
        nth_rw 1 [mul_comm]
        nth_rw 2 [mul_comm]
        assumption
        all_goals
          positivity
    -- Show that α ≥ 7 or β > 32.
    by_cases h₃ : α < 7
    . simp at h₃
      interval_cases α
      all_goals
        iterate 2 rw [div_lt_div_iff₀] at h₂
        norm_cast at h₂
        omega
      all_goals
        norm_num
    . -- If α ≥ 7, then β > 77 / 17 * α > 31, so β ≥ 32.
      suffices β > 31 by
        omega
      qify
      calc
        β > 77 / (17 : ℚ) * α := by
          nth_rw 2 [div_lt_div_iff₀] at h₂
          rw [gt_iff_lt, mul_comm, <-mul_div_assoc, div_lt_iff₀, mul_comm]
          exact h₂.2
          all_goals
            positivity
        _ ≥ 77 / (17 : ℚ) * 7 := by
          apply mul_le_mul_of_nonneg_left
          simp at h₃
          simp [h₃]
          norm_num
        _ > 31 := by
          norm_num
