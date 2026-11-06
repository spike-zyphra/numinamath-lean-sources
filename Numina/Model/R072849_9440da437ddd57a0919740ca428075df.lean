import Mathlib

open Real Set

theorem algebra_133741 (x : Fin 3 → ℝ) (h : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 0 * x 1 + x 1 * x 2 = 2) :
    |x 1| ≤ 2 := by
  have h1 : (x 0 + x 1 / 2) ^ 2 + (x 2 + x 1 / 2) ^ 2 + (x 1 ^ 2) / 2 = 2 := by 
    nlinarith
  have h2 : (x 0 + x 1 / 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h3 : (x 2 + x 1 / 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h4 : (x 1 ^ 2) / 2 ≤ 2 := by
    nlinarith
  have h5 : x 1 ^ 2 ≤ 4 := by
    nlinarith
  have h6 : |x 1| ≤ 2 := by
    have h7 : x 1 ^ 2 ≤ 4 := h5
    have h8 : -2 ≤ x 1 ∧ x 1 ≤ 2 := by
      constructor
      · nlinarith [sq_nonneg (x 1 + 2), sq_nonneg (x 1 - 2)]
      · nlinarith [sq_nonneg (x 1 + 2), sq_nonneg (x 1 - 2)]
    cases' abs_cases (x 1) with h9 h10
    · 
      linarith
    · 
      linarith
  exact h6