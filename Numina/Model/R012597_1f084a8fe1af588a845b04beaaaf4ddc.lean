import Mathlib

theorem algebra_315747 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h1 : 5 * x = 270 + 6 * y) (h2 : 3 * (x + 98) = 8 * y) :
    (x + 98) / x = 2 := by
  have eq1 : 5 * x = 270 + 6 * y := h1
  have eq2 : 3 * x + 294 = 8 * y := by
    linarith [h2]
  omega