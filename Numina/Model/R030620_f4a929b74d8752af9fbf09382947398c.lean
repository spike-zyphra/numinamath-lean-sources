import Mathlib

theorem number_theory_196393 (n : ℕ) (h₀ : n > 0) :
    ¬ ∃ m, m > 0 ∧ (n * (n + 1) * (n + 2) * (n + 3)) = m ^ 2 := by
  rintro ⟨m, hm₁, hm₂⟩
  have h1 : n * (n + 1) * (n + 2) * (n + 3) = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) := by 
    ring
  rw [h1] at hm₂
  have h2 : (n ^ 2 + 3 * n : ℕ) ^ 2 < (n * (n + 1) * (n + 2) * (n + 3)) := by
    nlinarith [sq_pos_of_pos h₀, sq_nonneg (n ^ 2 + 3 * n : ℕ), sq_nonneg (n : ℕ), sq_nonneg ((n + 1 : ℕ)), sq_nonneg ((n + 2 : ℕ)), sq_nonneg ((n + 3 : ℕ)), mul_pos (show 0 < n by linarith) (show 0 < n + 1 by nlinarith), mul_pos (show 0 < n by linarith) (show 0 < n + 2 by nlinarith), mul_pos (show 0 < n by linarith) (show 0 < n + 3 by nlinarith)]
  have h3 : (n * (n + 1) * (n + 2) * (n + 3)) < ((n ^ 2 + 3 * n + 1) : ℕ) ^ 2 := by
    nlinarith [sq_pos_of_pos h₀, sq_nonneg (n ^ 2 + 3 * n : ℕ), sq_nonneg (n ^ 2 + 3 * n + 1 : ℕ), sq_nonneg (n : ℕ), sq_nonneg ((n + 1 : ℕ)), sq_nonneg ((n + 2 : ℕ)), sq_nonneg ((n + 3 : ℕ)), mul_pos (show 0 < n by linarith) (show 0 < n + 1 by nlinarith), mul_pos (show 0 < n by linarith) (show 0 < n + 2 by nlinarith), mul_pos (show 0 < n by linarith) (show 0 < n + 3 by nlinarith)]
  have h4 : (n ^ 2 + 3 * n : ℕ) < m := by 
    nlinarith
  have h5 : m < ((n ^ 2 + 3 * n + 1) : ℕ) := by
    nlinarith
  have h6 : m < m := by
    nlinarith
  linarith