import Mathlib

theorem algebra_55244 {m n : ℤ} (hm : 0 < m) (hn : 0 < n) (hmn : m > n)
    (h : 3 * (3 * m * n - 2) ^ 2 - 2 * (3 * m - 3 * n) ^ 2 = 2019) :
    3 * m + n = 46 := by

  have h1 : 3 * m ^ 2 * n ^ 2 - 2 * m ^ 2 - 2 * n ^ 2 = 223 := by 
    ring_nf at h 
    nlinarith
  have h2 : m ≤ 31 := by
    by_contra h3 
    push_neg at h3 
    have h3 : m ≥ 32 := by nlinarith
    have h4 : n ≥ 1 := by linarith 
    nlinarith [sq_nonneg (m * n), sq_nonneg (m - 15), sq_nonneg (n - 1), 
        sq_nonneg (m^2 - 225), sq_nonneg (n^2 - 1), 
        mul_pos hm hn, sq_nonneg (m * n - 15), sq_nonneg (m - 15), sq_nonneg (n - 1)]
  have h3 : n ≤ 31 := by 
    by_contra h4 
    push_neg at h4 
    have h4 : n ≥ 32 := by nlinarith 
    have h4 : n ≥ 32 := by nlinarith 
    have h4 : m ≥ 33 := by nlinarith
    nlinarith [sq_nonneg (m * n), sq_nonneg (m - 15), sq_nonneg (n - 1), 
        sq_nonneg (m^2 - 225), sq_nonneg (n^2 - 1), 
        mul_pos hm hn, sq_nonneg (m * n - 15), sq_nonneg (m - 15), sq_nonneg (n - 1)]
  interval_cases m <;> try { 
    omega 
  } <;> try { 
    interval_cases n <;> omega 
  }