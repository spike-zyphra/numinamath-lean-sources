import Mathlib

theorem number_theory_114112 (n : ℕ) (h : n^2 = (2*n+1) * (2*n+3) * (2*n+5) * (2*n+7)) :
    n^2 = 9 := by
  have h1 : n ≤ 3 := by
    nlinarith [sq_nonneg (n - 0), sq_nonneg (n - 1), sq_nonneg (n - 2), sq_nonneg (n - 3),
      h, mul_pos (show (4 : ℕ) > 0 by norm_num) (show (n ^ 3) > 0 by
        nlinarith [pow_pos (show n > 0 by nlinarith) 3]
      )]
  interval_cases n <;> norm_num at h <;> try { norm_num at h; all_goals nlinarith }