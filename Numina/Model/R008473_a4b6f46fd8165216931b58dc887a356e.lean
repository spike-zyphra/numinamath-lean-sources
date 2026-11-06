import Mathlib

theorem algebra_10344 : IsLeast {t : ℝ | t ≥ 0 ∧ -16 * t ^ 2 + 80 * t = 36} 0.5 := by 
  constructor
  · -- Show that 0.5 is in the set
    constructor
    · norm_num -- 0.5 ≥ 0 
    · norm_num -- Check that -16 * (0.5)^2 + 80 * (0.5) = 36 
  · -- Show that ∀ t ∈ {t : ℝ | t ≥ 0 ∧ -16 * t ^ 2 + 80 * t = 36}, 0.5 ≤ t
    intro t ht
    rcases ht with ⟨htge, hteq⟩
    -- Let t be a solution to the equation such that t ≥ 0.
    -- We need to prove that 0.5 ≤ t
    nlinarith [sq_nonneg (t - 0.5), sq_nonneg (t - 4.5)]