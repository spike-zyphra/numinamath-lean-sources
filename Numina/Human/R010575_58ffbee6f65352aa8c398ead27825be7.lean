import Mathlib

theorem algebra_283360 (x y a b : ℝ) (hx : x > 0) (hy : y > 0)
    (ha : 0 < a) (hb : 0 < b) (hxy₁ : x = y + 32)
    (hxy₂ : x - (9 - 3) * a = y - (9 - 7) * b)
    (hxa : x = (10 - 3) * a) (hyb : y = (12 - 7) * b) :
    x + y = 52 := by
  linarith
