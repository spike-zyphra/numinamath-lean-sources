import Mathlib

theorem number_theory_298166 (n : ℕ) (hn : n > 0) (h1 : ∃ k, k^2 = n + 100) (h2 : ∃ m, m^2 = n + 168) :
    n = 156 := by 
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨m, hm⟩
  have h_eq1 : m^2 = k^2 + 68 := by
    nlinarith [hk, hm]
  have h_eq2 : m > k := by
    by_contra h
    push_neg at h
    have : m^2 ≤ k^2 := by nlinarith [h]
    omega
  have h_eq5 : k ≤ 34 := by 
    nlinarith [sq_nonneg (m - (k + 2)), sq_nonneg (k - 16), sq_nonneg (m - 18), h_eq1, show k < m by omega, sq_nonneg (m - k)]
  have h_eq6 : m ≤ 36 := by 
    nlinarith [h_eq1, h_eq5]
  interval_cases k <;> try { 
    have : m ≤ 36 := by nlinarith 
    interval_cases m <;> omega 
  }