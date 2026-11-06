import Mathlib

theorem algebra_303375 (n : ℕ) :
    ¬∃ m, (m * (m + 1)) = n^2 + 3 * n + 3 := by
  rintro ⟨m, hm⟩

  by_cases h : m ≤ n + 1
  · -- Assume m ≤ n + 1
    have h3 : m * (m + 1) ≤ (n + 1) * (n + 2) := by
      have h4 : m ≤ n + 1 := by linarith
      have h5 : m + 1 ≤ n + 2 := by linarith
      nlinarith [show m ≤ n + 1 by linarith, show m + 1 ≤ n + 2 by linarith, sq_nonneg (m - (n + 1) : ℤ), sq_nonneg (n + 1 : ℕ)]
    have h4 : (n + 1) * (n + 2) = n^2 + 3 * n + 2 := by
      nlinarith
    have h5 : m * (m + 1) < n^2 + 3 * n + 3 := by
      nlinarith [h4, h3]
    nlinarith
  · -- Assume m > n + 1
    have h6 : m ≥ n + 2 := by omega
    have h7 : m * (m + 1) ≥ (n + 2) * (n + 3) := by
      have h8 : m ≥ n + 2 := by linarith
      have h9 : m + 1 ≥ n + 3 := by linarith
      nlinarith [show m ≥ n + 2 by linarith, show m + 1 ≥ n + 3 by linarith, sq_nonneg (m - (n + 2) : ℤ), sq_nonneg (n + 2 : ℕ)]
    have h8 : (n + 2) * (n + 3) > n^2 + 3 * n + 3 := by
      nlinarith
    have h9 : m * (m + 1) > n^2 + 3 * n + 3 := by
      nlinarith [h8, h7]
    nlinarith