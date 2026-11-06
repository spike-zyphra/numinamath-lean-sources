import Mathlib

theorem algebra_318278 (x : ℝ) :
    x^2 - x + 1 = (x^2 + x + 1) * (x^2 + 2 * x + 4) ↔ x = -1 := by
  constructor
  · -- Forward direction: if the equation holds, then x = -1
    intro h

    have h1 : x^4 + 3 * x^3 + 6 * x^2 + 7 * x + 3 = 0 := by
      nlinarith [h, sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x^2 + x + 1), sq_nonneg (x^2 + 2 * x + 4)]

    have h2 : (x + 1)^2 * (x^2 + x + 3) = 0 := by
      nlinarith

    cases' (mul_eq_zero.1 h2) with h3 h4

    · -- Case where (x + 1)^2 = 0
      have h5 : x + 1 = 0 := by
        apply pow_eq_zero 
        exact h3
      linarith

    · -- Case where x^2 + x + 3 = 0
      have h5 : x^2 + x + 3 = 0 := by
        nlinarith

      nlinarith [sq_nonneg (x + 1 / 2)]

  · -- Backward direction: if x = -1, then the equation holds
    intro h
    rw [h]
    nlinarith