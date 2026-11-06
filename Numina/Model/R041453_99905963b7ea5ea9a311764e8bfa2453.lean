import Mathlib

theorem algebra_233736 (x : ℝ) (h1 : 2 * x ^ 3 + 4 * x ^ 2 + 4 * x - 10 ≠ 0) (h2 : 2 * x - 2 ≠ 0) :
    (6 * x ^ 3 + 13 * x ^ 2 + 15 * x - 25) / (2 * x ^ 3 + 4 * x ^ 2 + 4 * x - 10) =
    (6 * x - 5) / (2 * x - 2) := by
  -- To prove equality of fractions, cross multiply.
  -- Show that (6x^3 +13x^2 +15x -25)(2x -2) = (6x -5)(2x^3 +4x^2 +4x -10)
  have h3 : (2 * x ^ 3 + 4 * x ^ 2 + 4 * x - 10) ≠ 0 := h1
  have h4 : (2 * x - 2) ≠ 0 := h2
  field_simp [h1, h2]
  ring