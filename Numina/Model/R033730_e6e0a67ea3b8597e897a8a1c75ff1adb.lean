import Mathlib

theorem inequalities_604925 :
  IsGreatest {k : ℤ| ∀ m n : ℤ, 0 < m ∧ 0 < n ∧ (m + n)^2 < m^3 + n^3 →
  (m + n)^2 + k ≤ m^3 + n^3} 10 := by 
  constructor
  · -- Show 10 is in the set
    intro m n h
    rcases h with ⟨hm, hn, h1⟩
    by_contra h
    push_neg at h
    have h2 : m ≤ 5 := by
      nlinarith [sq_nonneg (m - 2 : ℤ), sq_nonneg (n - 3 : ℤ), sq_nonneg (m - 3 : ℤ), sq_nonneg (n - 2 : ℤ),
        sq_nonneg (m + n - 5 : ℤ), sq_nonneg (m - n : ℤ),
        h1, mul_pos hm hn
      ]
    have h3 : n ≤ 5 := by
      nlinarith [sq_nonneg (m - 2 : ℤ), sq_nonneg (n - 3 : ℤ), sq_nonneg (m - 3 : ℤ), sq_nonneg (n - 2 : ℤ),
        sq_nonneg (m + n - 5 : ℤ), sq_nonneg (m - n : ℤ),
        h1, mul_pos hm hn
      ]
    interval_cases m <;> interval_cases n <;> omega
  · -- Show 10 is greatest
    intro k hk
    have h23 := hk 2 3 ⟨by norm_num, by norm_num, by norm_num⟩
    norm_num at h23
    linarith