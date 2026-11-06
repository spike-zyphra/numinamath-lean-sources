import Mathlib

theorem number_theory_2882 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : x^2 + 6 * y^2 = 2022) : x + y = 47 := by
  have h1 : y ≤ 18 := by
    nlinarith [h, sq_nonneg (x)]
  have h2 : x ≤ 44 := by
    nlinarith [h, sq_nonneg (y)]
  interval_cases y <;> try { 
    interval_cases x <;> omega
  }
  all_goals try { 
    omega 
  }