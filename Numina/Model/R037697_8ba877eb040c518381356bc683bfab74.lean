import Mathlib

theorem number_theory_67773 (m n : ℕ) (hm : m > 0) (h1 : n > 1) (h2 : m^2 = 88 + n^2) : m = 13 ∨ m = 23 := by
  have h3 : m > n := by
    by_contra h
    push_neg at h
    have h4 : m ≤ n := by linarith
    have h5 : m^2 ≤ n^2 := by nlinarith
    have h6 : 88 + n^2 ≤ n^2 := by linarith [show 88 + n^2 = m^2 from by linarith, h5]
    have h7 : 88 ≤ 0 := by nlinarith
    linarith
  have h4 : m ≤ 44 := by
    nlinarith [show n > 1 from h1, sq_nonneg (m - n), sq_nonneg (m + n), show m ^ 2 - n ^ 2 = 88 by omega]
  have h6 : n ≤ 44 := by
    nlinarith [show m > n from h3, show m > 0 from hm, sq_nonneg (m - n), sq_nonneg (m + n), show m ^ 2 - n ^ 2 = 88 by omega]
  interval_cases m <;> try { 
    have h7 : n ≤ 44 := by
      nlinarith
    interval_cases n <;> omega 
  }