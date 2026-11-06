import Mathlib

/- 3A. If at least one of the numbers $a, b$ and $c$ is different from zero, then at least one of the numbers $(a+b+c)^{2}-8 a b,(a+b+c)^{2}-8 b c$ and $(a+b+c)^{2}-8 c a$ is positive. Prove! -/
theorem algebra_254105 {a b c : ℝ} (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    (a + b + c)^2 - 8 * a * b > 0 ∨ (a + b + c)^2 - 8 * b * c > 0 ∨
    (a + b + c)^2 - 8 * c * a > 0 := by
  -- first prove a^2 + b^2 + c^2 > 0, prove it by contradiciton, as a^2 + b^2 + c^2 ≤ 0 means a^2 + b^2 + c^2 = 0 and that means a = b = c = 0
  have : a^2 + b^2 + c^2 > 0 := by
    by_contra h'
    simp at h'
    have : a^2 + b^2 + c^2 ≥ 0 := by positivity
    have h': a^2 + b^2 + c^2 = 0 := by linarith
    have hz₁ : (a^2 + b^2 = 0) ∧ c^2 = 0 := by
      refine (add_eq_zero_iff_of_nonneg ?_ ?_).mp h'
      all_goals positivity
    have hz₂ : a^2 = 0 ∧ b^2 = 0 := by
      refine (add_eq_zero_iff_of_nonneg ?_ ?_).mp hz₁.left
      all_goals positivity
    have h₁ : a = 0 := by exact pow_eq_zero hz₂.left
    have h₂ : b = 0 := by exact pow_eq_zero hz₂.right
    have h₃ : c = 0 := by exact pow_eq_zero hz₁.right
    push_neg at h
    exact absurd h₃ (h h₁ h₂)

  -- next prove the goal by contradiction, i.e. assume all inequalities are ≤
  by_contra h'
  push_neg at h'
  -- add up the inequalities and factorize, from which we get a^2 + b^2 + c^2 ≤ 0, contradiction
  have : (a + b + c)^2 - 8 * a * b + (a + b + c)^2 - 8 * b * c + (a + b + c)^2 - 8 * c * a ≤ 0 := by linarith
  convert_to a^2 + b^2 + c^2 + (a-b)^2 + (b-c)^2 + (c-a)^2 ≤ 0 at this
  . ring
  . have : (a-b)^2 ≥ 0 := by positivity
    have : (b-c)^2 ≥ 0 := by positivity
    have : (c-a)^2 ≥ 0 := by positivity
    linarith