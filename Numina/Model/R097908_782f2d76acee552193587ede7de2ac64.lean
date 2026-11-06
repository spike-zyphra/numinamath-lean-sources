import Mathlib

theorem algebra_129305 (x y : ℝ) (h1 : x + y^2 = 1) (h2 : x^2 + y^3 = 1) :
    (x, y) = (1, 0) ∨ (x, y) = (-3, -2) ∨ (x, y) = (0, 1) := by
  have eq1 : x = 1 - y^2 := by linarith
  rw [eq1] at h2
  have h3 : y^4 + y^3 - 2 * y^2 = 0 := by
    nlinarith [sq_nonneg (y^2 : ℝ), sq_nonneg (y - 0 : ℝ), sq_nonneg (y - 1 : ℝ), sq_nonneg (y + 2 : ℝ)]
  have h4 : y^2 * (y^2 + y - 2) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with hy1 hy2
  · -- Case where $y^2 = 0$, so $y = 0$.
    have hy0 : y = 0 := by
      nlinarith
    have hx1 : x = 1 := by
      rw [hy0] at eq1
      nlinarith
    left
    simp [hx1, hy0]
  · -- Case where $y^2 + y - 2 = 0$.
    have hy3 : y^2 + y - 2 = 0 := by
      nlinarith
    have hy4 : (y - 1) * (y + 2) = 0 := by
      nlinarith [hy3]
    cases' (mul_eq_zero.mp hy4) with hy5 hy6
    · -- Case $y - 1 = 0$, so $y = 1$
      have hy1 : y = 1 := by
        nlinarith
      have hx0 : x = 0 := by
        rw [hy1] at eq1
        nlinarith
      right
      right
      simp [hx0, hy1]
    · -- Case $y + 2 = 0$, so $y = -2$
      have hy2 : y = -2 := by
        nlinarith
      have hx3 : x = -3 := by
        rw [hy2] at eq1
        nlinarith
      right
      left
      simp [hx3, hy2]