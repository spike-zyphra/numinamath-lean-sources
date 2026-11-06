import Mathlib

theorem algebra_209764 (a : ℝ) (h : ∃ x y, x ≠ y ∧ x^4 - 18 * x^3 + a * x^2 + 200 * x - 1984 = 0 ∧ y^4 - 18 * y^3 + a * y^2 + 200 * y - 1984 = 0 ∧ x * y = -32) :
    a = 86 := by
  rcases h with ⟨x, y, hxy, hx, hy, hxy2⟩
  have eq1 : (x - y) * ( (x + y) * (x^2 + y^2) - 18 * (x^2 + x * y + y^2) + a * (x + y) + 200 ) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
      intro h'
      apply hxy
      linarith
    ), sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x + y)]
  cases' (mul_eq_zero.mp eq1) with h1 h1
  · -- x - y = 0 is impossible
    have h2 : x - y ≠ 0 := by
      intro h'
      apply hxy
      linarith
    contradiction
  · -- The second factor is zero
    have eq2 : (x + y) * (x^2 + y^2) - 18 * (x^2 + x * y + y^2) + a * (x + y) + 200 = 0 := h1
    have h3 : x * y = -32 := hxy2
    have h4 : x^2 + y^2 = (x + y)^2 + 64 := by
      nlinarith [h3, sq_nonneg (x - y), sq_nonneg (x + y)]
    have h5 : x^2 + x * y + y^2 = (x + y)^2 + 32 := by
      nlinarith [h3, sq_nonneg (x - y), sq_nonneg (x + y)]
    rw [h4, h5] at eq2
    nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
      intro h'
      apply hxy
      linarith
    ), sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x^3 - y^3), sq_nonneg (x^4 - y^4), sq_nonneg (x - 2), sq_nonneg (y + 4)]