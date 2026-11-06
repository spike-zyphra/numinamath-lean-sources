import Mathlib

theorem algebra_306871 (a : ℝ) (ha : a ≠ 0) (x₁ x₂ : ℝ)
    (hx₁ : a * x₁ ^ 2 + (a + 2) * x₁ + 9 * a = 0) (hx₂ : a * x₂ ^ 2 + (a + 2) * x₂ + 9 * a = 0)
    (hne : x₁ ≠ x₂) (hord : x₁ < 2 / 5 ∧ 2 / 5 < x₂) :
    -2 / 11 < a ∧ a < 0 := by
  have h1 : a ≠ 0 := ha
  have h2 : x₁ - x₂ ≠ 0 := by
    intro h
    have h' : x₁ = x₂ := by linarith
    contradiction
  have h3 : (x₁ - x₂) * (a * (x₁ + x₂) + a + 2) = 0 := by
    nlinarith [hx₁, hx₂]
  have h4 : a * (x₁ + x₂) + a + 2 = 0 := by
    apply (mul_left_inj' h2).mp
    linarith
  -- From h4 we can derive $\quad a < 0$
  have h5 : a < 0 := by
    nlinarith [sq_pos_of_ne_zero (show x₁ - x₂ ≠ 0 by exact h2), sq_nonneg (a), sq_nonneg (x₁ - x₂), sq_nonneg (a * (x₁ - x₂)), sq_nonneg (x₁ + x₂), sq_nonneg (a * (x₁ + x₂)), sq_nonneg ((a + 2) * (x₁ - x₂)), hord.1, hord.2]
  -- Now show $\quad -\frac{2}{11} < a$
  have h8 : -2 / 11 < a := by
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact h1), sq_nonneg (x₁ - 2 / 5), sq_nonneg (x₂ - 2 / 5), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (a * (x₁ - x₂)), sq_nonneg ((a + 2) * (x₁ - x₂)), hord.1, hord.2]
  constructor
  · exact h8
  · exact h5