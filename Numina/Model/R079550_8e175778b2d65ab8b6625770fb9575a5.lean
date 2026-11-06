import Mathlib

theorem algebra_4539 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : 6 * (x + 4 * y) = x ^ 2 + y ^ 2 + 153) : x + y = 15 := by
  have h1 : (x - 3) ^ 2 + (y - 12) ^ 2 = 0 := by
    nlinarith 
  have h2 : (x - 3) ^ 2 ≥ 0 := by
    apply sq_nonneg 
  have h3 : (y - 12) ^ 2 ≥ 0 := by
    apply sq_nonneg 
  have h4 : (x - 3) ^ 2 = 0 := by
    linarith 
  have h5 : (y - 12) ^ 2 = 0 := by
    linarith 
  have h6 : x - 3 = 0 := by 
    rwa [sq_eq_zero_iff] at h4 
  have h7 : y - 12 = 0 := by 
    rwa [sq_eq_zero_iff] at h5 
  linarith