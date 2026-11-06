import Mathlib

theorem algebra_308480 (x y : ℝ) :
    (x + 3)^2 + y^2 + (x - y)^2 = 3 ↔ (x = -2 ∧ y = -1) := by
  constructor
  · -- Assume (x + 3)^2 + y^2 + (x - y)^2 = 3, prove (x = -2 ∧ y = -1)
    intro h
    have eq1 : (x + 3)^2 + y^2 + (x - y)^2 = 3 := h
    have eq2 : 2 * x^2 + 6 * x + 9 + 2 * y^2 - 2 * x * y = 3 := by
      nlinarith [eq1]
    have eq3 : 2 * x^2 + 6 * x + 6 + 2 * y^2 - 2 * x * y = 0 := by
      linarith [eq2]
    have eq4 : x^2 + 3 * x + 3 + y^2 - x * y = 0 := by
      nlinarith [eq3]
    have h1 : (y + 1)^2 = 0 := by
      nlinarith [sq_nonneg (x - (-2)), sq_nonneg (y - (-1)), sq_nonneg (x - y - (-2 - (-1))), sq_nonneg (x + 2 - y - 1)]
    have hy1 : y + 1 = 0 := by
      nlinarith
    have hy2 : y = -1 := by linarith
    have hx1 : x + 2 = 0 := by
      rw [hy2] at eq4
      nlinarith [sq_nonneg (x + 2)]
    have hx2 : x = -2 := by linarith
    exact ⟨hx2, hy2⟩
  · -- Assume (x = -2 ∧ y = -1), prove (x + 3)^2 + y^2 + (x - y)^2 = 3
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    nlinarith