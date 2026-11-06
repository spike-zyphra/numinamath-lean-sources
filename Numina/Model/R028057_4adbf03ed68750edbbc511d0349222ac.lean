import Mathlib

theorem algebra_307328 (a : ℝ) (ha : a ≠ 0) (x₁ x₂ : ℝ)
    (hx₁ : a * x₁ ^ 2 + (a + 1) * x₁ + 6 * a = 0)
    (hx₂ : a * x₂ ^ 2 + (a + 1) * x₂ + 6 * a = 0)
    (hne : x₁ ≠ x₂) (hord : x₁ < 1 ∧ 1 < x₂) :
    -1 / 8 < a ∧ a < 0 := by

  have h1 : a * x₁ ^ 2 + (a + 1) * x₁ + 6 * a = 0 := hx₁
  have h2 : a * x₂ ^ 2 + (a + 1) * x₂ + 6 * a = 0 := hx₂

  have h3 : x₁ < 1 := hord.left
  have h4 : 1 < x₂ := hord.right

  have h5 : -1 / 8 < a := by
    by_contra h6
    push_neg at h6
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show (x₁ - x₂) ≠ 0 by 
      intro h
      apply hne
      linarith
    ), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ + 1), sq_nonneg (a), sq_nonneg (x₁ - 1), sq_nonneg (x₂ - 1)]

  have h14 : a < 0 := by
    by_contra h5
    push_neg at h5
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show (x₁ - x₂) ≠ 0 by 
      intro h
      apply hne
      linarith
    ), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ + 1), sq_nonneg (a), sq_nonneg (x₁ - 1), sq_nonneg (x₂ - 1)]

  constructor
  · -- Show that $ -1/8 < a $.
    linarith
  · -- Show that $ a < 0 $.
    linarith