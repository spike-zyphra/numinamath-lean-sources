import Mathlib

theorem number_theory_288742 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
(h : a^2 + b^2 + c^2 + d^2 = 70) :
a + b + c + d ≤ 16 := by

  by_contra h5
  push_neg at h5
  have h5' : a + b + c + d ≥ 17 := by
    omega
  have h6 : (a + b + c + d) ^ 2 ≥ 289 := by 
    nlinarith
  have h7 : (a + b + c + d) ^ 2 ≤ 280 := by 
    nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a - c : ℤ), sq_nonneg (a - d : ℤ), sq_nonneg (b - c : ℤ), sq_nonneg (b - d : ℤ), sq_nonneg (c - d : ℤ), h]
  nlinarith