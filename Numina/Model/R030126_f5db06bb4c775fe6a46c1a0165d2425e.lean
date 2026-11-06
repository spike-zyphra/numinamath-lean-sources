import Mathlib

theorem number_theory_274 (a b c : ℕ) (ha : 1 < a) (hb : a < b) (hc : b < c)
  (h1 : a + b + c = 111) (h2 : b^2 = a * c) : b = 36 := by
  have h3 : c = 111 - a - b := by 
    omega 
  rw [h3] at h2
  have h7 : a ≤ 36 := by
    nlinarith [h1, sq_nonneg (a - 36 : ℤ), sq_nonneg (b - 36 : ℤ), sq_nonneg (c - 36 : ℤ)]
  have h8 : b ≤ 36 := by
    nlinarith [h1, sq_nonneg (a - 36 : ℤ), sq_nonneg (b - 36 : ℤ), sq_nonneg (c - 36 : ℤ)]
  interval_cases b <;> try { 
    interval_cases a <;> omega 
  }