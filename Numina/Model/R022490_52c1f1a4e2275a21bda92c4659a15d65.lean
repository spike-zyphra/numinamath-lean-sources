import Mathlib

theorem number_theory_50951 {n : ℤ} (hn : ∃ k l, n - 76 = k^3 ∧ n + 76 = l^3 ∧ k > 0 ∧ l > 0) :
    n = 140 := by
  rcases hn with ⟨k, l, h1, h2, hk, hl⟩
  have h3 : l^3 - k^3 = 152 := by 
    linarith
  have h4 : l > k := by
    nlinarith [sq_pos_of_pos (show (0 : ℤ) < l by linarith), sq_pos_of_pos (show (0 : ℤ) < k by linarith), sq_nonneg (l - k), sq_nonneg (l + k)]
  have h5 : l ≤ 19 := by
    nlinarith [sq_nonneg (l - k), sq_nonneg (l + k), sq_nonneg (k ^ 2 - l ^ 2), sq_nonneg (k * l), sq_nonneg (k - 12), sq_nonneg (l - 6), sq_nonneg (k + l), sq_nonneg (k - 20), sq_nonneg (l - 8), h3]
  have h6 : k ≤ 19 := by
    nlinarith [sq_nonneg (l - k), sq_nonneg (l + k), sq_nonneg (k ^ 2 - l ^ 2), sq_nonneg (k * l), sq_nonneg (k - 12), sq_nonneg (l - 6), sq_nonneg (k + l), sq_nonneg (k - 20), sq_nonneg (l - 8), h3]
  interval_cases k <;> try { 
    interval_cases l <;> omega
  }