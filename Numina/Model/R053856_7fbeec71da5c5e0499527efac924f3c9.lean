import Mathlib

theorem number_theory_298668 (n : ℕ) (hn : n > 0) :
    ∃ m : ℕ, m > 0 ∧ ∃ k : ℕ, k > 0 ∧ n^6 + 3 * m = k^3 := by 
  use 3 * n^4 + 9 * n^2 + 9
  constructor
  · -- Show m > 0 
    nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n), hn]
  · -- Show existence of k
    use n^2 + 3
    constructor
    · -- Show k > 0
      have h1 : n ^ 2 ≥ 1 := by
        have : n ≥ 1 := by linarith
        nlinarith [sq_nonneg (n)]
      nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n), hn]
    · -- Show n^6 + 3 * m = k^3
      ring_nf