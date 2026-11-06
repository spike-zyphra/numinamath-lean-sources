import Mathlib
/-let a^2+b^2=1(b≠ 0), if the line ax+by=2 and the ellipse x^2/6+y^2/2=1 have common points, then the range of a/b is ?-/
theorem algebra_272908 (a b : ℝ) (h₀ : a^2 + b^2 = 1) (h₁ : b ≠ 0)
    (h₂ : ∃ x y, a * x + b * y = 2 ∧ x^2 / 6 + y^2 / 2 = 1) :
    a / b ≤ -1 ∨ a / b ≥ 1 := by
  rcases h₂ with ⟨x, y, hline, heldipse⟩
  -- key lemma, prove by completing square.
  have h3 : b^2 + 3 * a^2 ≥ 2 := by
    nlinarith [sq_nonneg (x - 3 * a), sq_nonneg (y - b), sq_nonneg (a * x + b * y - 2), sq_nonneg (x^2 / 6 + y^2 / 2 - 1),
      h₀, sq_nonneg (a), sq_nonneg (b), sq_nonneg (x), sq_nonneg (y)]
  have h4 : a^2 ≥ 1 / 2 := by nlinarith [h₀, h3]
  have h5 : b^2 > 0 := by
    have h6 : b^2 ≥ 0 := sq_nonneg b
    by_contra h
    push_neg at h
    have : b^2 = 0 := by linarith
    have hb : b = 0 := pow_eq_zero this
    contradiction
  have h6 : a^2 ≥ b^2 := by nlinarith [h₀, h4]
  have h7 : a / b ≤ -1 ∨ a / b ≥ 1 := by
    by_contra h
    push_neg at h
    have h1 : a / b > -1 := h.1
    have h2 : a / b < 1 := h.2
    have h3 : (a / b) ^ 2 < 1 := by nlinarith [sq_nonneg (a / b), h1, h2]
    have h4 : (a / b) ^ 2 ≥ 1 := by
      have h5 : a^2 / b^2 ≥ 1 := by
        have h6 : a^2 ≥ b^2 := by nlinarith [h₀, h4]
        have h7 : b^2 > 0 := by
          exact h5
        have h8 : a^2 / b^2 ≥ 1 := by
          apply (le_div_iff₀ h7).mpr
          nlinarith
        exact h8
      have h9 : (a / b) ^ 2 = a^2 / b^2 := by
        field_simp [h₁]
      nlinarith [h6, h9]
    nlinarith [h3, h4]
  exact h7
