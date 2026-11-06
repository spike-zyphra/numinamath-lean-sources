import Mathlib

theorem algebra_87072 {x y : ℝ} (h1 : x^3 + y^3 = 19) (h2 : x^2 + y^2 + 5 * x + 5 * y + x * y = 12) :
    (x, y) = (3, -2) ∨ (x, y) = (-2, 3) := by
  have h3 : x + y = 1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1)]
  have h4 : x * y = -6 := by
    have h5 : (x + y) ^2 + 5 * (x + y) - (x * y) = 12 := by
      nlinarith [h2, h3]
    rw [show x + y = 1 by linarith [h3]] at h5
    linarith
  have h5 : (x - 3) * (x + 2) = 0 := by
    have h6 : y = 1 - x := by linarith [h3]
    rw [h6] at h4
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- h6 : x - 3 = 0 ⇒ x = 3
    have hx : x = 3 := by linarith
    have hy : y = -2 := by linarith [h3, hx]
    left
    simp [hx, hy]
  · -- h7 : x + 2 = 0 ⇒ x = -2
    have hx : x = -2 := by linarith
    have hy : y = 3 := by linarith [h3, hx]
    right
    simp [hx, hy]