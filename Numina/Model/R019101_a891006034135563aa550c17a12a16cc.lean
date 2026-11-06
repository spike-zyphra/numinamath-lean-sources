import Mathlib

theorem algebra_326054 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x * y + x + y = 71) (h2 : x^2 * y + x * y^2 = 880) :
    x^2 + y^2 = 146 := by
  have h3 : x * y * (x + y) = 880 := by
    nlinarith
  have h4 : x ≤ 35 := by
    nlinarith [h1, mul_pos hx hy]
  have h5 : y ≤ 35 := by
    nlinarith [h1, mul_pos hx hy]
  interval_cases x <;> interval_cases y
    <;> omega