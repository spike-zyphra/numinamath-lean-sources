import Mathlib

theorem algebra_120898 (a b c : ℝ) (h₀ : a + b + c > 0) (h₁ : a * b + b * c + c * a > 0)
    (h₂ : a * b * c > 0) :
    a > 0 ∧ b > 0 ∧ c > 0 := by
  have h3 : a > 0 := by
    by_contra ha
    push_neg at ha
    have h3 : b * c < 0 := by
      nlinarith [h₂, sq_nonneg (a), sq_nonneg (b + c), sq_nonneg (b - c),
          sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
    have h4 : a * (b + c) ≤ 0 := by
      nlinarith [ha, h₀, sq_nonneg (a), sq_nonneg (b + c)]
    nlinarith
  have h4 : b > 0 := by
    by_contra hb
    push_neg at hb
    have h3 : a * c < 0 := by
      nlinarith [h₂, sq_nonneg (b), sq_nonneg (a + c), sq_nonneg (a - c),
          sq_nonneg (a * b), sq_nonneg (c * b), sq_nonneg (a * c)]
    have h4 : b * (a + c) ≤ 0 := by
      nlinarith [hb, h₀, sq_nonneg (b), sq_nonneg (a + c)]
    nlinarith
  have h5 : c > 0 := by
    by_contra hc
    push_neg at hc
    have h3 : a * b < 0 := by
      nlinarith [h₂, sq_nonneg (c), sq_nonneg (a + b), sq_nonneg (a - b),
          sq_nonneg (a * c), sq_nonneg (b * c), sq_nonneg (a * b)]
    have h4 : c * (a + b) ≤ 0 := by
      nlinarith [hc, h₀, sq_nonneg (c), sq_nonneg (a + b)]
    nlinarith
  exact ⟨h3, h4, h5⟩