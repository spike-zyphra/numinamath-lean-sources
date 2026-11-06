import Mathlib

theorem algebra_318690 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : ∃ x : ℕ, x > 0 ∧ x^2 - m * n * x + (m + n) = 0) :
    (m, n) = (5, 1) ∨ (m, n) = (2, 2) ∨ (m, n) = (3, 2) := by 
  rcases h with ⟨x, hx_pos, heq⟩
  have h_eq4 : m * n * x = x^2 + (m + n) := by
    omega
  have bound1 : m ≤ 7 := by
    nlinarith [sq_nonneg (m - 1 : ℤ), sq_nonneg (n - 1 : ℤ), 
      sq_nonneg (m * n - 4 : ℤ),
      sq_nonneg (x * 1 - 1 : ℤ)]
  have bound2 : n ≤ 7 := by
    nlinarith [sq_nonneg (m - 1 : ℤ), sq_nonneg (n - 1 : ℤ), 
      sq_nonneg (m * n - 4 : ℤ),
      sq_nonneg (x * 1 - 1 : ℤ)]
  interval_cases m <;> interval_cases n <;> try { 
    omega
  }