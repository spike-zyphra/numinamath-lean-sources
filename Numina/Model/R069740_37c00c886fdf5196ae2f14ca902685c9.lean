import Mathlib

theorem algebra_230201 (x y : ℝ) (hx : 3 * x + 2 * y ≠ 0) (hy : 3 * x - 2 * y ≠ 0) :
    (7 * x - 5 * y) / (3 * x + 2 * y) + (5 * x - 8 * y) / (3 * x - 2 * y) -
    (x - 9 * y) / (3 * x + 2 * y) - (8 * x - 10 * y) / (3 * x - 2 * y) = 1 := by
  have h1 : 3 * x + 2 * y ≠ 0 := hx
  have h2 : 3 * x - 2 * y ≠ 0 := hy
  field_simp [h1, h2]
  ring