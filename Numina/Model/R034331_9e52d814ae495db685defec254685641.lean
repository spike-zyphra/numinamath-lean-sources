import Mathlib

theorem algebra_119143 (a b c d : ℝ) (h₁ : ¬∃ x : ℝ, x^2 + a * x + b = 0)
    (h₂ : ¬∃ x : ℝ, x^2 + c * x + d = 0) :
    ¬∃ x : ℝ, x^2 + (a + c) / 2 * x + (b + d) / 2 = 0 := by
  by_contra h
  rcases h with ⟨x, hx⟩
  have h1 : a ^ 2 - 4 * b < 0 := by
    by_contra h'
    push_neg at h'
    have h3 : ∃ x : ℝ, x^2 + a * x + b = 0 := by
      use (-a + Real.sqrt (a ^ 2 - 4 * b)) / 2
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * b), Real.sq_sqrt (show a ^ 2 - 4 * b ≥ 0 by linarith)]
    contradiction
  have h2 : c ^ 2 - 4 * d < 0 := by
    by_contra h'
    push_neg at h'
    have h3 : ∃ x : ℝ, x^2 + c * x + d = 0 := by
      use (-c + Real.sqrt (c ^ 2 - 4 * d)) / 2
      nlinarith [Real.sqrt_nonneg (c ^ 2 - 4 * d), Real.sq_sqrt (show c ^ 2 - 4 * d ≥ 0 by linarith)]
    contradiction
  have h3 : (a + c) ^ 2 < 8 * (b + d) := by
    nlinarith [sq_nonneg (x + (a + c) / 4), sq_nonneg (x + (a + c) / 4), h1, h2, sq_nonneg (a - c), sq_nonneg (a - c)]
  -- We can complete the square to show a contradiction
  have h4 : 4 * x ^ 2 + 2 * (a + c) * x + 2 * (b + d) = 0 := by
    linarith [hx]
  nlinarith [sq_nonneg (x + (a + c) / 4), sq_nonneg (a - c), sq_nonneg (x + (a + c) / 4), h1, h2, sq_nonneg (2 * x + (a + c))]