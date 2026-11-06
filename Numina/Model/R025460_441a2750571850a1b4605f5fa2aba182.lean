import Mathlib

/- Given that $m, n, k$ are positive integers, if there exists a pair of positive integers $(a, b)$ satisfying $ ( 1 + a ) n ^ { 2 } - 4 ( m + a ) n + 4 m ^ { 2 } + 4 a + b ( k - 1 ) ^ { 2 } < 3 , $ then the number of possible values for $ m + n + k $ is ___          ___. -/
theorem inequalities_10279 (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (h : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (1 + a) * n ^ 2 - 4 * (m + a) * n + 4 * m ^ 2 + 4 * a + b * (k - 1) ^ 2 < 3) :
    m + n + k = 3 ∨ m + n + k = 4 ∨ m + n + k = 5 ∨ m + n + k = 6 := by
  rcases h with ⟨a, b, ha, hb, h⟩
  have h1 : (1 + a) * n ^ 2 - 4 * (m + a) * n + 4 * m ^ 2 + 4 * a + b * (k - 1) ^ 2 < 3 := h
  have h3 : m ≤ 3 := by
    by_contra h4
    push_neg at h4
    have h4 : m ≥ 4 := by omega
    have h5 : (1 + a) * n ^ 2 - 4 * (m + a) * n + 4 * m ^ 2 + 4 * a + b * (k - 1) ^ 2 ≥ 3 := by
      nlinarith [sq_nonneg (n * (1 + a) - (m + a) * 2), sq_nonneg ((k : ℕ) - 1), sq_nonneg ((n) - ((m + a) / (1 + a))), sq_pos_of_pos ha, sq_pos_of_pos hb
      ]
    omega
  have h4 : n ≤ 3 := by
    by_contra h5
    push_neg at h5
    have h5 : n ≥ 4 := by omega
    have h5 : (1 + a) * n ^ 2 - 4 * (m + a) * n + 4 * m ^ 2 + 4 * a + b * (k - 1) ^ 2 ≥ 3 := by
      nlinarith [sq_nonneg (n * (1 + a) - (m + a) * 2), sq_nonneg ((k : ℕ) - 1), sq_nonneg ((n) - ((m + a) / (1 + a))), sq_pos_of_pos ha, sq_pos_of_pos hb
      ]
    omega
  have h5 : k ≤ 6 := by
    by_contra h6
    push_neg at h6
    have h6 : k ≥ 7 := by omega
    have h6 : (1 + a) * n ^ 2 - 4 * (m + a) * n + 4 * m ^ 2 + 4 * a + b * (k - 1) ^ 2 ≥ 3 := by
      nlinarith [sq_nonneg (n * (1 + a) - (m + a) * 2), sq_nonneg ((k : ℕ) - 1), sq_nonneg ((n) - ((m + a) / (1 + a))), sq_pos_of_pos ha, sq_pos_of_pos hb
      ]
    omega
  interval_cases m <;> interval_cases n <;> interval_cases k <;> omega