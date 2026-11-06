import Mathlib

theorem algebra_136586 (x1 x2 x3 x4 : ℝ)
    (h1 : x1 + 2 * x2 - 3 * x3 - x4 = 10)
    (h2 : -2 * x1 - 3 * x2 + 7 * x3 = -23)
    (h3 : 2 * x1 + 6 * x2 - 5 * x3 - 5 * x4 = 18)
    (h4 : -x1 + 3 * x3 - 4 * x4 = -11) :
    x1 = -2 ∧ x2 = 2 ∧ x3 = -3 ∧ x4 = 1 := by
  have hx1 : x1 = -2 := by
    linarith [h1, h2, h3, h4]
  have hx2 : x2 = 2 := by
    linarith [h1, h2, h3, h4]
  have hx3 : x3 = -3 := by
    linarith [h1, h2, h3, h4]
  have hx4 : x4 = 1 := by
    linarith [h1, h2, h3, h4]
  exact ⟨hx1, hx2, hx3, hx4⟩