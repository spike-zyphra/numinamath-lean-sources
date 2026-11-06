import Mathlib

theorem algebra_310358 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (h1 : x * y + x + y = 71) (h2 : x^2 * y + x * y^2 = 830) :
    x^2 + y^2 = 146 := by 
  have h3 : x ≤ 35 := by
    nlinarith [h1, mul_pos hx hy]
  have h4 : y ≤ 35 := by
    nlinarith [h1, mul_pos hx hy]
  interval_cases x <;> try { 
    omega
  } 
  <;> interval_cases y 
  <;> omega