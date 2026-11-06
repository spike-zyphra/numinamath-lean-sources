import Mathlib

theorem algebra_14493 (x₀ y₀ r : ℝ) (hr : r > 0) (h : ∀ x y, 9 * x^2 - 18 * x + 9 * y^2 + 36 * y + 44 = 0 ↔ (x - x₀)^2 + (y - y₀)^2 = r^2) :
    (x₀, y₀) = (1, -2) := by
  have eq1 := h (4 / 3) (-2)
  norm_num at eq1
  have eq2 := h 1 (-5 / 3)
  norm_num at eq2
  have eq3 := h (2 / 3) (-2)
  norm_num at eq3
  have eq4 : x₀ = 1 := by
    nlinarith
  have eq5 : y₀ = -2 := by
    nlinarith
  simp [Prod.ext_iff, eq4, eq5]