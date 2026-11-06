import Mathlib

theorem number_theory_1915 :
IsLeast {A | ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ 80 * n = m ^ 4 ∧ A = m + n} 135 := by
  constructor
  · -- Show that 135 is in the set.
    exact ⟨10, 125, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that it's minimal.
    intro A h
    rcases h with ⟨m, n, hm1, hn1, heq1, hA⟩
    by_contra h
    push_neg at h
    have h1 : m + n < 135 := by
      linarith [h, hA]
    have h3 : m ≤ 10 := by
      nlinarith [sq_nonneg (m - 10 : ℤ), sq_nonneg (n - 125 : ℤ),
        sq_nonneg (m ^ 2 - 100 : ℤ), sq_nonneg (m - 10 : ℤ),
        sq_nonneg (m * (m - 10) : ℤ), sq_nonneg (n * (m - 10) : ℤ),
        sq_nonneg ((n - 125) * m : ℤ),
        sq_nonneg ((m - 10) * (n - 125) : ℤ),
        heq1, hm1, hn1]
    have h4 : m ≥ 1 := by
      linarith
    interval_cases m <;> omega