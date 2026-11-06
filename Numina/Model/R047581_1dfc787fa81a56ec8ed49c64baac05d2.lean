import Mathlib

theorem number_theory_176299 (n d : ℕ) (h₀ : n > 0) (h₁ : (10 * n + d) ^ 2 - n ^ 2 = 8 * n) :
    n = 2 ∧ d = 3 ∨ n = 3 ∧ d = 4 ∨ n = 4 ∧ d = 2 := by 
  have eq1 : (10 * n + d) ^ 2 = n ^ 2 + 8 * n := by
    omega
  have eq2 : (9 * n + d) * (11 * n + d) = 8 * n := by 
    nlinarith [eq1]
  have h3 : n ≤ 9 := by
    by_contra h4
    push_neg at h4
    have h4 : n ≥ 10 := by omega
    have h5 : (9 * n + d) * (11 * n + d) ≥ 9900 := by
      nlinarith [show d ≥ 0 by omega, sq_nonneg (d : ℕ), sq_nonneg (n : ℕ), mul_pos (show 0 < (1 : ℕ) by omega) (show 0 < (1 : ℕ) by omega), h4]
    nlinarith [eq2, h4, sq_nonneg (d : ℕ), sq_nonneg (n : ℕ)]
  have h4 : d ≤ 9 := by
    by_contra h5
    push_neg at h5
    have h5 : d ≥ 10 := by omega
    nlinarith [eq2, h5, sq_nonneg (d : ℕ), sq_nonneg (n : ℕ), mul_pos (show 0 < (1 : ℕ) by omega) (show 0 < (1 : ℕ) by omega)]
  interval_cases n <;> try { 
    omega
  }
  <;> interval_cases d 
    <;> omega