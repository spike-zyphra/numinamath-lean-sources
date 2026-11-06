import Mathlib

theorem algebra_15192 (x y : ℝ) :
    y^4 - 4 * x^4 = 2 * y^2 - 1 ↔ (y^2 - 2 * x^2 = 1 ∨ y^2 + 2 * x^2 = 1) := by
  constructor
  · -- Forward direction: assume the given equation, prove the disjunction
    intro h_eq
    have h_eq1 : (y^2 - 1) ^ 2 = 4 * x^4 := by
      nlinarith [sq_nonneg (y^2 - 1), sq_nonneg (2 * x^2)]
    have h_eq2 : y^2 - 1 = 2 * x^2 ∨ y^2 - 1 = -2 * x^2 := by
      have h : (y^2 - 1 - 2 * x^2) * (y^2 - 1 + 2 * x^2) = 0 := by
        nlinarith [h_eq1]
      cases' (mul_eq_zero.1 h) with h1 h2
      · left
        linarith
      · right
        linarith
    cases' h_eq2 with h_eq2_1 h_eq2_2
    · -- Case where \( y^2 - 1 = 2x^2 \), which implies \( y^2 - 2x^2 = 1 \)
      left
      nlinarith
    · -- Case where \( y^2 - 1 = -2x^2 \), which implies \( y^2 + 2x^2 = 1 \)
      right
      nlinarith
  · -- Backward direction: assume the disjunction, prove the given equation
    rintro (h_eq | h_eq)
    · -- Case where \( y^2 - 2x^2 = 1 \)
      nlinarith [sq_nonneg (y^2 - 1), sq_nonneg (2 * x^2), h_eq]
    · -- Case where \( y^2 + 2x^2 = 1 \)
      nlinarith [sq_nonneg (y^2 - 1), sq_nonneg (2 * x^2), h_eq]