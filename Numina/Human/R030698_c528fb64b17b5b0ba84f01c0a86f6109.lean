import Mathlib

/-Impossible Square. Prove that for no positive integer 
n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 is a perfect square.-/
theorem number_theory_269835 (n : ℤ) (hn : n > 0) :
    ¬ ∃ k, k^2 = n^4 + 2*n^3 + 2*n^2 + 2*n + 1 := by
  intro h
  rcases h with ⟨k, hk⟩
  -- we show that it's between two squares
  have h1 : n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 > (n^2 + n)^2 := by
    nlinarith [sq_nonneg (n + 1), sq_nonneg (n ^ 2), sq_nonneg (n), hn]
  have h2 : n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 < (n^2 + n + 1)^2 := by
    nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n), hn]
  have h3 : k^2 > (n^2 + n) ^ 2 := by linarith [h1, hk]
  have h4 : k^2 < (n^2 + n + 1) ^ 2 := by linarith [h2, hk]
  by_cases hk' : k ≥ 0
  · -- Case k ≥ 0
    have h5 : n^2 + n < k := by
      nlinarith [sq_nonneg (k - (n^2 + n)), h3]
    have h6 : k < n^2 + n + 1 := by
      nlinarith [sq_nonneg (k - (n^2 + n + 1)), h4]
    omega -- Contradiction since n^2 + n < k < n^2 + n + 1 for integer k
  · -- Case k < 0
    have h5 : n^2 + n < -k := by
      nlinarith [sq_nonneg (k + (n^2 + n)), h3]
    have h6 : -k < n^2 + n + 1 := by
      nlinarith [sq_nonneg (k + (n^2 + n + 1)), h4]
    omega -- Contradiction since n^2 + n < -k < n^2 + n + 1 for integer -k