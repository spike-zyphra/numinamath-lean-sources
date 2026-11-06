import Mathlib

theorem inequalities_80884 (k m n : ℤ) (hk : k > 0) (hm : m > 0) (hn : n > 0)
    (h : m^2 + n = k^2 + k) : m ≤ n := by
  have h1 : n = k^2 + k - m^2 := by
    linarith
  have h3 : k ≥ m := by
    by_contra h4
    push_neg at h4
    have h5 : m ≥ k + 1 := by omega
    have h5' : m^2 ≥ (k + 1)^2 := by nlinarith [ sq_nonneg (m - (k + 1)) ]
    have h4 : k < m := by linarith
    have h7 : n ≤ 0 := by
      nlinarith [ sq_nonneg (k - m), sq_nonneg (m - k - 1) ]
    linarith
  have h2 : m ≤ n := by 
    have h5 : n = k^2 + k - m^2 := by 
      linarith
    nlinarith [ sq_nonneg (m - k), sq_nonneg (k - m), sq_nonneg (m - 1), sq_nonneg (k - 1) ]
  linarith