import Mathlib

theorem number_theory_46964 {m n : ℤ} (hm : m > 0) (hn : n > 0)
    (h : m ^ 4 - n ^ 4 = 3439) : m * n = 90 := by
  have h1 : m ^ 4 = n^4 + 3439 := by
    linarith
  have h2 : m > n := by
    by_contra h2
    push_neg at h2
    have h3 : m ≤ n := by linarith
    have h4 : m ^ 4 ≤ n ^ 4 := by
      apply pow_le_pow_left
      all_goals nlinarith
    have h5 : m ^ 4 - n ^ 4 ≤ 0 := by linarith
    have h6 : m ^ 4 - n ^ 4 > 0 := by linarith
    linarith
  have h3 : n < m := by linarith
  have h4 : m ≤ 20 := by
    nlinarith [sq_nonneg (m ^ 2 - n ^ 2), sq_nonneg (m - 10 : ℤ), sq_nonneg (n - 9 : ℤ),
          sq_nonneg (m + n - 19 : ℤ), sq_nonneg (m - n - 1 : ℤ),
          sq_nonneg (m ^ 2 - n ^ 2), sq_nonneg (m ^ 2 + n ^ 2 - 181 : ℤ)]
  have h5 : n ≤ 20 := by
    nlinarith [sq_nonneg (m ^ 2 - n ^ 2), sq_nonneg (m - 10 : ℤ), sq_nonneg (n - 9 : ℤ),
          sq_nonneg (m + n - 19 : ℤ), sq_nonneg (m - n - 1 : ℤ),
          sq_nonneg (m ^ 2 - n ^ 2), sq_nonneg (m ^ 2 - 9^2), sq_nonneg (n ^ 2 : ℤ)]
  interval_cases m <;> interval_cases n <;> omega