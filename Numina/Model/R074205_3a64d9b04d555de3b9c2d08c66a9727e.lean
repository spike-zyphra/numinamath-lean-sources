import Mathlib

theorem number_theory_3611 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
(ha1 : a ≥ b) (h : a^2 + b^2 = 2017) : a = 44 := by
  have h1 : a ≤ 44 := by
    nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ)]
  have h2 : b ≤ 44 := by
    nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ)]
  interval_cases a <;> try { 
    interval_cases b <;> omega 
  }