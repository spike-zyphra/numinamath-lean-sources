import Mathlib

theorem number_theory_150825 (n : ℤ) (hn : 11 < n) :
    ¬∃ m, m ^ 2 = n ^ 2 - 19 * n + 89 := by
  rintro ⟨m, hm⟩
  have h2 : m ^ 2 = n ^ 2 - 19 * n + 89 := by linarith
  have h3 : m ^ 2 > (n - 10) ^ 2 := by
    nlinarith
  have h5 : m > n - 10 ∨ m < -(n - 10) := by
    have h7 : m ^ 2 > (n - 10) ^ 2 := h3
    have h8 : m > n - 10 ∨ m < -(n - 10) := by
      by_contra h
      push_neg at h
      have h9 : m ≤ n - 10 := by linarith
      have h10 : m ≥ - (n - 10) := by linarith
      nlinarith [sq_nonneg (m - (n - 10)), sq_nonneg (m + (n - 10)), sq_nonneg (m - (n - 10)), sq_nonneg (m + (n - 10))]
    assumption
  have h6 : m < n - 9 := by
    nlinarith
  rcases h5 with h7 | h8
  · 
    have h9 : m > n - 10 := h7
    have h11 : m ≤ n - 10 := by
      omega
    nlinarith
  · 
    have h10 : m < -(n - 10) := h8
    nlinarith [sq_nonneg (m + (n - 10)), sq_nonneg (m + (n - 10)), sq_nonneg (m - (n - 10)), sq_nonneg (m - (n - 10)), sq_nonneg (n - 10 - m), sq_nonneg (n - 9 - m)]