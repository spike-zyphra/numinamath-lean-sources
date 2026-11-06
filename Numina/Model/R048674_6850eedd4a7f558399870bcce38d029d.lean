import Mathlib

theorem algebra_2116 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : 1 / x + 1 / y = 5) :
    (2 * x - 5 * x * y + 2 * y) / (x + 2 * x * y + y) = 5 / 7 := by
  have h1 : x + y = 5 * x * y := by
    field_simp [hx, hy] at h
    linarith
  have h2 : 2 * x - 5 * x * y + 2 * y = 5 * x * y := by
    linarith [h1]
  have h3 : x + 2 * x * y + y = 7 * x * y := by
    have : x + y = 5 * x * y := h1
    linarith [this]
  rw [h2, h3]
  have h4 : x * y ≠ 0 := by
    apply mul_ne_zero
    exact hx
    exact hy
  field_simp [h4]
  all_goals linarith