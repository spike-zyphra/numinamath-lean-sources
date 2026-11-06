import Mathlib

theorem other_71584 (a d : ℚ) (h₀ : a > 0) (h₁ : d > 0)
    (h₂ : 1 / a = 1 / 3 + d) (h₃ : 1 / (a + d) = 1 / 4 + d)
    (h₄ : 1 / (a + 2 * d) = 1 / 6 + d) :
    ∑ i ∈ Finset.range 4, (1 / (a + i * d)) = 25 := by

  have eq1 : a ≠ 0 := by
    linarith
  have eq2 : a + d ≠ 0 := by
    nlinarith
  have eq3 : a + 2 * d ≠ 0 := by
    nlinarith
  have eq4 : a + 3 * d ≠ 0 := by
    nlinarith

  field_simp [eq1, eq2, eq3] at h₂ h₃ h₄

  -- This should be a direct approach
  norm_num [Finset.sum_range_succ]
  <;> nlinarith [sq_nonneg (a - 12), sq_nonneg (d + 1 / 12), sq_nonneg (d), sq_nonneg (a - 3), sq_nonneg (a + d - 4), sq_nonneg (a + 2 *d - 6)]