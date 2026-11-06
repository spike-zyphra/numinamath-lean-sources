import Mathlib

theorem algebra_325974 (a b : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1)
    (h₁ : ∃ x, f x = 0) :
    a ^ 2 - b ≥ 1 := by
  rcases h₁ with ⟨x, hx⟩
  have hfx : f x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 := h₀ x
  rw [hfx] at hx
  by_cases h2 : x = 0
  · -- x = 0
    rw [h2] at hx
    nlinarith
  · -- x ≠ 0
    have h3 : x ≠ 0 := h2
    have eq_b : b = (-x^4 - a * x^3 - a * x - 1) / x^2 := by
      field_simp [h3]
      linarith
    rw [eq_b]
    have h4 : a ^ 2 - (-x^4 - a * x^3 - a * x - 1) / x^2 ≥ 1 := by
      have h5 : x ^ 2 > 0 := by
        exact sq_pos_of_ne_zero h3
      have h6 : a ^ 2 - (-x^4 - a * x^3 - a * x - 1) / x^2 - 1 ≥ 0 := by
        have h8 : x ^ 2 > 0 := by
          exact sq_pos_of_ne_zero h3
        have h9 : (x ^ 2) * (a ^ 2 - (-x^4 - a * x^3 - a * x - 1) / x^2 - 1) ≥ 0 := by
          have : (x ^ 2) * (a ^ 2 - (-x^4 - a * x^3 - a * x - 1) / x^2 - 1) =
                (x ^ 4 + a * x^3 + a * x + 1 + a ^ 2 * x^2 - x^2) := by
            field_simp [h8] at *
            linarith
          rw [this]
          nlinarith [sq_nonneg (a * x + (x^2 + 1) / 2), sq_nonneg (x^2 - 1)]
        nlinarith [h8]
      linarith
    linarith