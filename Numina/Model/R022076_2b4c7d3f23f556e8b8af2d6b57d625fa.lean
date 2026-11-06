import Mathlib

theorem algebra_311501 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b^2 - 2 * c - 2 = 0) (h2 : 3 * a^2 - 8 * b + c = 0) :
    a * b * c ≤ 2013 := by
  have eq1 : c = 8 * b - 3 * a^2 := by 
    nlinarith
  rw [eq1] at h1
  have h3 : 6 * a^2 + a + (b^2 - 16 * b - 2) = 0 := by
    nlinarith
  have h4 : b ≤ 15 := by 
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 11), sq_nonneg (c - 61)]
  have h5 : b ≥ 1 := by 
    linarith
  interval_cases b <;> try { 
    ring_nf at h3 
    have h6 : a ≤ 15 := by 
      nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 11), sq_nonneg (c - 61)]
    have h7 : a ≥ 1 := by 
      linarith
    interval_cases a <;> omega 
  }