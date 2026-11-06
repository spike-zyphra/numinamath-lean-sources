import Mathlib

theorem algebra_20169 {m n : ℤ} (hm : 0 < m) (hn : 0 < n)
    (h : 6 * m * n = 27 - 3 * m - 2 * n) :
    (m, n) = (1, 3) := by
  have h1 : 6 * m * n + 3 * m + 2 * n = 27 := by
    linarith
  have h2 : m ≤ 4 := by
    nlinarith [mul_pos hm hn, sq_nonneg (m - 4 : ℤ), sq_nonneg (n - 1 : ℤ)]
  have h3 : n ≤ 13 := by
    nlinarith [mul_pos hm hn, sq_nonneg (m - 1 : ℤ), sq_nonneg (n - 13 : ℤ)]
  have h4 : m ≥ 1 := by linarith
  have h5 : n ≥ 1 := by linarith
  interval_cases m <;> try { 
    omega 
  } <;> try { 
    interval_cases n <;> norm_num at h1 
    <;> try { 
      simp [Prod.ext_iff] at *
      all_goals 
        try { 
          omega 
        } 
        <;> try { 
          tauto 
        }
    }
  }