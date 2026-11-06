import Mathlib

theorem algebra_110282 {x y : ℕ} (hx : x + y = 20) (hy : x > 0) (hxy : y > 0)
    (h : x^2 - y^2 = 120) : x = 13 := by
  have h1 : x ≤ 20 := by 
    omega
  have h2 : y < 20 := by
    omega
  interval_cases x <;> try { 
    omega 
  }
  <;> interval_cases y 
    <;> omega