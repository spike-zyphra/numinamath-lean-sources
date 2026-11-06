import Mathlib

theorem algebra_301633 (n : ℕ) (hn : n > 0) :
    ¬ ∃ m, m^2 = n^4 + 2*n^3 + 2*n^2 + 2*n + 1 := by
  rintro ⟨m, hm⟩
  have h₁ : m^2 = n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 := by
    linarith
  have h₂ : (n^2 + n) ^ 2 < n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 := by
    nlinarith [sq_pos_of_pos (show (0 : ℕ) < n by linarith [hn]), sq_nonneg (n + 1), sq_pos_of_pos (show (0 : ℕ) < n + 1 by linarith [hn]), sq_nonneg (n)]
  have h₃ : n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 < (n^2 + n + 1) ^ 2 := by
    nlinarith [sq_pos_of_pos (show (0 : ℕ) < n by linarith [hn]), sq_nonneg (n + 1), sq_pos_of_pos (show (0 : ℕ) < n + 1 by linarith [hn]), sq_nonneg (n)]
  have h₄ : (n^2 + n) ^ 2 < m^2 := by
    linarith
  have h₅ : m^2 < (n^2 + n + 1) ^ 2 := by
    linarith
  have h6 : n^2 + n < m := by
    nlinarith [sq_nonneg (n ^ 2 + n), sq_nonneg (m), sq_nonneg (n + 1), sq_nonneg (m - (n ^ 2 + n)), sq_nonneg (n)]
  have h7 : m < n^2 + n + 1 := by
    nlinarith [sq_nonneg (n ^ 2 + n + 1), sq_nonneg (m), sq_nonneg (n + 1), sq_nonneg (n), sq_nonneg ( (n^2 +n +1) - (m) ), sq_nonneg (m)]
  omega