import Mathlib

theorem algebra_9682 {x y : ℤ} (h1 : y = 18*x^2-25*x-39) (h2 : y = 3*x^3+29*x^2-35*x+11) :
    x=-5 := by
  have eq : 3 * x^3 + 29 * x^2 - 35 * x + 11 = 18 * x^2 - 25 * x - 39 := by
    rw [← h1, h2]
  have eq2 : 3 * x^3 + 11 * x^2 - 10 * x + 50 = 0 := by
    nlinarith [eq]
  have h3 : (x + 5) * (3 * x^2 - 4 * x + 10) = 0 := by
    nlinarith [eq2]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case where $x + 5 = 0$, so $x = -5$.
    linarith
  · -- Case where $3x^2 - 4x + 10 = 0$.
    have h6 : 3 * x^2 - 4 * x + 10 = 0 := h5
    have h8 : 3 * x^2 - 4 * x + 10 > 0 := by
      nlinarith [sq_nonneg (3 * x - 2)]
    linarith