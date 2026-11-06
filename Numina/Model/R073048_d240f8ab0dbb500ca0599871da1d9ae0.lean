import Mathlib

theorem algebra_6350 {x y : ℤ} (hxpos : 0 < x) (hypos : x < y) (h1 : x + y^2 = 55) (h2 : x^2 + y^3 = 379) : x = 6 := by
  have h3 : y > 0 := by linarith [hxpos, hypos]
  have h4 : y ≤ 7 := by 
    nlinarith [h1, sq_nonneg (y : ℤ), sq_nonneg (x : ℤ)]
  have h5 : y ≥ 1 := by nlinarith [h3]
  interval_cases y <;> 
    try { 
      nlinarith 
    }
  <;> omega