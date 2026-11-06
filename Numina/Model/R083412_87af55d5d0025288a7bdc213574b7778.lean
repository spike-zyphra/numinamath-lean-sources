import Mathlib

open Real

theorem inequalities_132836 (x : ℝ) (hx : x > 0) :
    x^2 + 1 / x^2 ≥ 2 ∧ x^2 ≥ 2 * x - 2 ∧ x^4 - 2 * x^3 + x^2 ≥ 0 := by
  have h1 : x ^ 2 + 1 / x ^ 2 ≥ 2 := by
    have h2 : x ^ 2 + 1 / x ^ 2 - 2 ≥ 0 := by
      have h3 : x ^ 2 + 1 / x ^ 2 - 2 = (x ^ 4 - 2 * x ^ 2 + 1) / x ^ 2 := by
        field_simp
        ring
      rw [h3]
      have h4 : x ^ 4 - 2 * x ^ 2 + 1 ≥ 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2), sq_nonneg (x - 1), sq_nonneg (x + 1)]
      have h5 : x ^ 2 > 0 := by 
        exact sq_pos_of_pos hx
      apply div_nonneg
      · exact h4
      · nlinarith [h5]
    linarith
  have h2 : x ^ 2 ≥ 2 * x - 2 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x * (x - 1)), sq_nonneg (x + 1)]
  have h3 : x^4 - 2 * x^3 + x^2 ≥ 0 := by
    nlinarith [sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1), sq_nonneg (x ^ 2), sq_nonneg (x * (x - 1))]
  constructor
  · exact h1
  constructor
  · exact h2
  · exact h3