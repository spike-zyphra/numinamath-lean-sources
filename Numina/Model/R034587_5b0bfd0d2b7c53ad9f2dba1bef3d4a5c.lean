import Mathlib

theorem algebra_187162 (x y : ℝ) (h1 : x^4 - y^4 = 15) (h2 : x^3 * y - x * y^3 = 6) :
    (x, y) = (-2, -1) ∨ (x, y) = (2, 1) := by
  have eq3 : 2 * (x^2) - 5 * x * y + 2 * (y^2) = 0 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 2 * y), sq_nonneg (2 * x - y)]

  have eq4 : (2 * x - y) * (x - 2 * y) = 0 := by
    nlinarith

  cases' (mul_eq_zero.1 eq4) with h4 h5
  · -- Case where 2x - y = 0, so y = 2x
    have hy : y = 2 * x := by linarith
    rw [hy] at h1 h2
    have h3 : x ^ 4 = -1 := by
      nlinarith
    have h4 : x ^ 4 ≥ 0 := by positivity
    nlinarith [sq_nonneg (x ^ 2)]
  · -- Case where x - 2y = 0, so x = 2y
    have hx : x = 2 * y := by linarith
    rw [hx] at h1 h2
    have h3 : y ^ 4 = 1 := by
      nlinarith
    have h4 : y^2 = 1 := by
      have h5 : y ^ 4 = 1 := h3
      have h6 : y ^ 2 ≥ 0 := by positivity
      have h7 : (y ^ 2) ^ 2 = 1 := by
        nlinarith
      have h8 : y ^ 2 = 1 := by
        have h9 : (y ^ 2) ^ 2 - 1 = 0 := by linarith
        have h10 : (y ^ 2 - 1) * (y ^ 2 + 1) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h10) with h11 h12
        · -- Case where $y^2 - 1 = 0$
          linarith
        · -- Case where $y^2 + 1 = 0$
          nlinarith [sq_nonneg y]
      linarith
    have hy1 : y = 1 ∨ y = -1 := by
      have h5 : y ^ 2 = 1 := h4
      have : y = 1 ∨ y = -1 := by
        have h6 : y ^ 2 - 1 = 0 := by linarith
        have h7 : (y - 1) * (y + 1) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h7) with h8 h9
        · -- Case where $y - 1 = 0$
          left
          linarith
        · -- Case where $y + 1 = 0$
          right
          nlinarith
      exact this
    cases' hy1 with h7 h8
    · -- If $y = 1$, then $x = 2 * 1 = 2$
      have hx2 : x = 2 := by
        nlinarith
      right
      simp [hx2, h7]
    · -- If $y = -1$, then $x = 2 * (-1) = -2$
      have hx2 : x = -2 := by
        nlinarith
      left
      simp [hx2, h8]