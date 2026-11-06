import Mathlib

theorem algebra_246110 (p : ℝ) (x₁ x₂ : ℝ)
    (h₁ : x₁ * (2 * x₁ - 3 * p) - 3 * p * (x₁ - 3 * p) = x₁ - 1)
    (h₂ : x₂ * (2 * x₂ - 3 * p) - 3 * p * (x₂ - 3 * p) = x₂ - 1) :
    |x₁ ^ 2 + x₂ ^ 2| > 1 ↔ p < -1 / 12 ∨ p > 7 / 12 := by
  have eq1 : 2 * x₁ ^ 2 - (6 * p + 1) * x₁ + (9 * p ^ 2 + 1) = 0 := by
    nlinarith [h₁]
  have eq2 : 2 * x₂ ^ 2 - (6 * p + 1) * x₂ + (9 * p ^ 2 + 1) = 0 := by
    nlinarith [h₂]
  have h3 : x₁ ^ 2 + x₂ ^ 2 = 3 * p - 3 / 4 := by
    have eq5 : x₁ + x₂ = (6 * p + 1) / 2 := by
      have eq4 : 2 * x₁ ^ 2 - (6 * p + 1) * x₁ + (9 * p ^ 2 + 1) - (2 * x₂ ^ 2 - (6 * p + 1) * x₂ + (9 * p ^ 2 + 1)) = 0 := by
        nlinarith [eq1, eq2]
      have h : 2 * (x₁ ^ 2 - x₂ ^ 2) - (6 * p + 1) * (x₁ - x₂) = 0 := by
        nlinarith [eq4]
      have h2 : (x₁ - x₂) * (2 * (x₁ + x₂) - (6 * p + 1)) = 0 := by
        linarith [h]
      cases (mul_eq_zero.mp h2) with
      | inl h3 =>
        -- x₁ - x₂ = 0
        have h6 : x₁ = x₂ := by linarith
        have h7 : (6 * p + 1) ^ 2 - 8 * (9 * p ^ 2 + 1) > 0 := by
          nlinarith [sq_pos_of_pos (show 0 < (1 : ℝ) by linarith), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - (6 * p + 1) / 2)]
        nlinarith [h6, sq_nonneg (x₁ - x₂)]
      | inr h4 =>
        -- 2 * (x₁ + x₂) - (6 * p + 1) = 0
        linarith
    have eq6 : x₁ * x₂ = (9 * p ^ 2 + 1) / 2 := by
      have eq3 : x₁ + x₂ = (6 * p + 1) / 2 := eq5
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - (6 * p + 1) / 2), sq_nonneg (x₁ * x₂), eq1, eq2, eq3]
    nlinarith [sq_nonneg (x₁ - x₂), eq6, eq5]
  rw [show x₁ ^ 2 + x₂ ^ 2 = 3 * p - 3 / 4 by linarith [h3]]
  constructor
  · -- Forward implication: if |3p - 3/4| > 1, then p < -1/12 or p > 7/12.
    intro h
    have h2 : |(3 * p - 3 / 4 : ℝ)| > (1 : ℝ) := by
      simpa using h
    cases' abs_cases (3 * p - 3 / 4) with h1 h1
    · -- $3p - 3/4 \geq 0$, so $|3p - 3/4| > 1 \implies 3p - 3/4 > 1$.
      right
      linarith
    · -- $3p - 3/4 < 0$, so $|3p - 3/4| > 1 \implies -(3p - 3/4) > 1$.
      left
      linarith
  · -- Backward implication: if p < -1/12 or p > 7/12, then |3p - 3/4| > 1.
    intro h
    cases' h with h4 h4
    · -- $p < -1/12$
      have h1 : |(3 * p - 3 / 4 : ℝ)| > (1 : ℝ) := by
        rw [abs_of_neg (by nlinarith)]
        nlinarith
      simpa using h1
    · -- $p > 7/12$
      have h1 : |(3 * p - 3 / 4 : ℝ)| > (1 : ℝ) := by
        rw [abs_of_pos (by nlinarith)]
        nlinarith
      simpa using h1