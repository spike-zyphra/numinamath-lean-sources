import Mathlib

theorem algebra_289155 (a b : ℝ) (h : ∃ x : ℝ, x^4 - a * x^3 + 2 * x^2 - b * x + 1 = 0) :
    a^2 + b^2 ≥ 8 := by
  rcases h with ⟨x, hx⟩
  have h1 : x^4 - a * x^3 + 2 * x^2 - b * x + 1 = 0 := hx
  have h2 : (x^2 + 1) ^ 2 = a * x^3 + b * x := by
    nlinarith
  have h3 : (x^2 + 1) ^ 4 ≤ (a^2 + b^2) * (x^6 + x^2) := by
    have h4 : (a * x^3 + b * x) ^ 2 ≤ (a^2 + b^2) * (x^6 + x^2) := by
      nlinarith [sq_nonneg (a * x^2 - b), sq_nonneg (a * x - b * x^3), sq_nonneg (x^3 * b - a * x), sq_nonneg (x^3 * a - b * x), sq_nonneg (x^2 * a - x * b), sq_nonneg (x^2 * b - x * a), sq_nonneg (x^2 * (x^2)), sq_nonneg ((x ^ 2) * (x ^ 2)), sq_nonneg (x ^ 2 - x ^ 2)]
    have h5 : (a * x^3 + b * x) ^ 2 = (x^2 + 1) ^ 4 := by
      have h6 : a * x^3 + b * x = (x^2 + 1) ^ 2 := by
        linarith [h2]
      rw [h6]
      all_goals nlinarith
    nlinarith [h5, h4]
  have h4 : (x^2 + 1) ^ 4 ≥ 8 * (x^6 + x^2) := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 4 - 2 * x ^ 2 + 1), sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 3 - x)]
  have h5 : x^6 + x^2 > 0 := by
    have h9 : x ^ 2 > 0 := by
      by_contra h10
      push_neg at h10
      have h10 : x ^ 2 = 0 := by nlinarith [sq_nonneg x, h10]
      have h11 : x = 0 := by nlinarith
      rw [h11] at h1
      nlinarith
    have h10 : x^6 + x^2 ≥ x ^ 2 := by
      nlinarith [sq_nonneg (x ^ 3), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 0), sq_nonneg (x ^ 2), sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 3), sq_nonneg (x ^ 3 - x), sq_nonneg (x ^ 2 - 1)]
    nlinarith
  have h8 : (a^2 + b^2) ≥ 8 := by
    nlinarith [show (x^6 + x^2) > 0 by linarith [h5]]
  linarith