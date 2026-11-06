import Mathlib

theorem algebra_87100 {x y : ℤ} (hy : 0 < y) (hxy : y < x) (hsum : x + y + x * y = 80) :
    x = 26 := by 
  have h3 : x ≥ 2 := by 
    nlinarith [hy, hxy]
  have h4 : x ≤ 80 := by 
    nlinarith [hsum]
  have h5 : y ≥ 1 := by 
    omega
  have h6 : y ≤ 80 := by 
    nlinarith [hsum]
  interval_cases x <;> omega