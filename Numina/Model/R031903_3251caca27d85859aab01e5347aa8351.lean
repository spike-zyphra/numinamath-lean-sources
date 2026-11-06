import Mathlib

theorem algebra_142724 (b k : ℝ) (h₀ : b ≠ 0) (h₁ : k ≠ 0)
    (h₂ : ∀ x, x^2 - b * x = k * x ∨ -x^2 + b * x = k * x ∨ x^2 - b * x = -k * x ∨
      -x^2 + b * x = -k * x) :
    {x | ∃ y, x^2 - b * x = y ∨ -x^2 + b * x = y ∨ y = k * x}.encard ≤ 9 := by
  exfalso
  specialize h₂ (b)
  by_cases h5 : (b : ℝ) ^ 2 - b * (b : ℝ) = k * (b : ℝ)
  · -- Assume h5
    have h6 : k = 0 := by
      apply (mul_right_inj' h₀).mp
      linarith
    contradiction
  · -- Assume h5 is false, so from the disjunction, either h6, h7, or h8 must hold
    by_cases h6 : - (b : ℝ) ^ 2 + b * (b : ℝ) = k * (b : ℝ)
    · -- Assume h6
      have h7 : k = 0 := by
        apply (mul_right_inj' h₀).mp
        linarith
      contradiction
    · -- Assume h6 is false, so either h7 or h8 must hold
      by_cases h7 : (b : ℝ) ^ 2 - b * (b : ℝ) = -k * (b : ℝ)
      · -- Assume h7
        have h8 : k = 0 := by
          apply (mul_right_inj' h₀).mp
          linarith
        contradiction
      · -- Assume h7 is false, so h8 must hold
        have h8 : - (b : ℝ) ^ 2 + b * (b : ℝ) = -k * (b : ℝ) := by
          tauto
        have h9 : k = 0 := by
          apply (mul_right_inj' h₀).mp
          linarith
        contradiction