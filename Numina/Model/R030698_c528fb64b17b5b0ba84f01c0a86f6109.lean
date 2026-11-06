import Mathlib

theorem number_theory_269835 (n : ℤ) (hn : n > 0) :
    ¬ ∃ k, k^2 = n^4 + 2*n^3 + 2*n^2 + 2*n + 1 := by 
  rintro ⟨k, hk⟩
  have h1 : k^2 = n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 := by
    linarith [hk]
  have h2 : (n^2 + n) ^ 2 < k^2 := by
    nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n), sq_nonneg (k - (n^2 + n)), sq_nonneg (n + 1),
        sq_nonneg (k), sq_nonneg ((n^2 + n + 1) - k), sq_nonneg (k + (n^2 + n)), hn]
  have h3 : k^2 < (n^2 + n + 1) ^ 2 := by
    nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n), sq_nonneg (k - (n^2 + n + 1)), sq_nonneg (n + 1),
        sq_nonneg (k), sq_nonneg ((n^2 + n) - k), sq_nonneg (k + (n^2 + n + 1)), hn]
  by_cases h : k ≥ 0
  · -- k ≥ 0
    have h4 : n^2 + n < k := by
      nlinarith [h2, h]
    have h5 : k < n^2 + n + 1 := by
      nlinarith [h3, h]
    omega
  · -- k < 0
    have h4 : n^2 + n < -k := by
      nlinarith [h2, sq_nonneg k, sq_nonneg (k + 0), show k < 0 by linarith]
    have h5 : -k < n^2 + n + 1 := by
      nlinarith [h3, sq_nonneg k, sq_nonneg (k + 0), show k < 0 by linarith]
    omega