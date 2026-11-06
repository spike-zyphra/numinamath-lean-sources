import Mathlib

theorem algebra_3922 {x y : ℤ} (hx : 0 < x) (hy : 10 < y)
    (h : 2 * x ^ 2 + 5 * x * y + 2 * y ^ 2 = 770) :
    x = 3 := by

  have h2 : x ≤ 19 := by
    nlinarith [sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 16 : ℤ), sq_nonneg (x * y), sq_nonneg ((x - y) : ℤ), sq_nonneg ((x + y) : ℤ)]
  have h4 : y ≤ 32 := by
    nlinarith [sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 16 : ℤ), sq_nonneg (x * y), sq_nonneg ((x - y) : ℤ), sq_nonneg ((x + y) : ℤ)]
  have h5 : x > 0 := hx
  have h6 : y > 10 := hy
  interval_cases x <;> try { 
    omega 
  } <;> try { 
    interval_cases y <;> omega 
  }