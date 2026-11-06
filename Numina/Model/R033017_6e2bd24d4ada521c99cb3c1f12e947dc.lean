import Mathlib

/- Given ${{x}^{2}}+3x+1=0$, then ${{x}^{2}}+\frac{1}{{{x}^{2}}}=$ ___          ___ , ${{x}^{3}}+\frac{1}{{{x}^{3}}}=$ ___          ___. -/
theorem algebra_3957 {x : ℝ} (hx : x^2 + 3 * x + 1 = 0) (hx2 : x ≠ 0) :
    x^2 + 1 / x^2 = 7 ∧ x^3 + 1 / x^3 = -18 := by

  -- First, prove that x + 1/x = -3
  have h1 : x + 1 / x = -3 := by
    have h2 : x ≠ 0 := hx2
    have h3 : x^2 + 1 = -3 * x := by
      linarith

    have h4 : x + 1 / x = -3 := by
      field_simp [h2] at h3 ⊢
      linarith

    exact h4

  -- Prove that x^2 + 1/x^2 = 7
  have h2₁ : x^2 + 1 / x^2 = 7 := by
    have h3 : x + 1 / x = -3 := h1
    have h4 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by
      field_simp [hx2]
      <;> ring

    rw [h4, h3]
    all_goals norm_num

  -- Prove that x^3 + 1/x^3 = -18
  have h3₁ : x^3 + 1 / x^3 = -18 := by
    have h4 : x + 1 / x = -3 := h1
    have h5 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp [hx2]
      <;> ring

    rw [h5, h4]
    all_goals norm_num

  -- Combine both results
  exact ⟨h2₁, h3₁⟩