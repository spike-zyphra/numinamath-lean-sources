import Mathlib

theorem algebra_321233 (a : ℝ) (ha : a ≠ 0) (x₁ x₂ : ℝ)
    (hx₁ : a * x₁ ^ 2 + (a + 2) * x₁ + 9 * a = 0) (hx₂ : a * x₂ ^ 2 + (a + 2) * x₂ + 9 * a = 0)
    (hne : x₁ ≠ x₂) (hord : x₁ < 1 ∧ 1 < x₂) :
    -2 / 11 < a ∧ a < 0 := by

  have h1 : a * x₁ ^ 2 + (a + 2) * x₁ + 9 * a = 0 := hx₁
  have h2 : a * x₂ ^ 2 + (a + 2) * x₂ + 9 * a = 0 := hx₂

  have h3 : a * (x₁ ^ 2 - x₂ ^ 2) + (a + 2) * (x₁ - x₂) = 0 := by
    have eq1 : a * x₁ ^ 2 + (a + 2) * x₁ + 9 * a = 0 := hx₁
    have eq2 : a * x₂ ^ 2 + (a + 2) * x₂ + 9 * a = 0 := hx₂
    have eq3 : a * x₁ ^ 2 + (a + 2) * x₁ + 9 * a - (a * x₂ ^ 2 + (a + 2) * x₂ + 9 * a) = 0 := by linarith
    have eq4 : a * (x₁ ^ 2 - x₂ ^ 2) + (a + 2) * (x₁ - x₂) = 0 := by
      nlinarith
    linarith [eq4]

  have h4 : a * (x₁ + x₂) + (a + 2) = 0 := by
    apply (mul_left_inj' (show x₁ - x₂ ≠ 0 by
      intro h
      apply hne
      linarith
    )).mp
    linarith

  have h5 : (a + 2) ^ 2 - 36 * a ^ 2 > 0 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero (show (x₁ - x₂) ≠ 0 by
      intro h
      apply hne
      linarith
    ), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (a * (x₁ - x₂)), sq_nonneg (a * (x₁ + x₂)), sq_nonneg ((a)), sq_nonneg ((a + 2))]

  have h6 : a < 0 := by
    nlinarith [hord.1, hord.2, sq_nonneg (x₁ - 1), sq_nonneg (x₂ - 1), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero (show (x₁ - x₂) ≠ 0 by
      intro h
      apply hne
      linarith
    ), sq_nonneg (a), sq_nonneg (a + 2)]

  have h7 : -2 / 11 < a := by
    nlinarith [hord.1, hord.2, sq_nonneg (x₁ - 1), sq_nonneg (x₂ - 1), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero (show (x₁ - x₂) ≠ 0 by
      intro h
      apply hne
      linarith
    ), sq_nonneg (a), sq_nonneg (a + 2)]

  constructor
  · -- -2/11 < a
    linarith [h7]
  · -- a < 0
    linarith [h6]