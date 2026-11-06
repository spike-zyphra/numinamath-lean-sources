import Mathlib

theorem algebra_229272 (a b c d : ℤ) (h₀ : Even a) (h₁ : Even b) (h₂ : Even c) (h₃ : Even d)
    (h₄ : 0 < a) (h₅ : a < b) (h₆ : b < c) (h₇ : c < d) (h₈ : d - a = 90)
    (h₉ : ∃ d, b = a + d ∧ c = b + d) (h₁₀ : ∃ r, c = b * r ∧ d = c * r) :
    a + b + c + d = 194 := by
  rcases h₉ with ⟨d₁, h₁₁, h₁₂⟩
  rcases h₁₀ with ⟨r, h₇₁, h₇₂⟩
  have eq1 : c = a + 2 * d₁ := by
    nlinarith
  have eq2 : b * r = a + 2 * d₁ := by
    have h₁₃ : c = b * r := by
      linarith [h₇₁]
    rw [h₁₃] at eq1
    linarith
  have eq3 : b * r^2 = a + 90 := by 
    have h₇₃ : d = c * r := by 
      linarith [h₇₂]
    have h₇₄ : c = b * r := by
      linarith [h₇₁]
    rw [h₇₄] at h₇₃
    have h₇₅ : d = b * r^2 := by
      rw [h₇₃]
      ring
    have h₇₆ : d = a + 90 := by
      linarith [h₈]
    rw [h₇₅] at h₇₆
    linarith
  have h₂₈ : r = 2 := by
    nlinarith [h₄, h₅, h₆, h₇, h₀, h₁, h₂, h₃, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (r : ℤ), sq_nonneg (d₁ : ℤ), sq_nonneg (a - 10), sq_nonneg (b - 10), sq_nonneg (c - 10), sq_nonneg (d - 10)]
  have eq4 : a + b + c + d = 194 := by
    rw [h₂₈] at eq2 eq3
    nlinarith [h₄, h₅, h₆, h₇, h₀, h₁, h₂, h₃, h₈, h₁₁, h₁₂, h₇₁, h₇₂]
  exact eq4