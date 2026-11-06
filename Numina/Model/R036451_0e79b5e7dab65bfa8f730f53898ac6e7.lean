import Mathlib

theorem number_theory_199733 (n : ℕ) (h : n > 0) :
    (n + 2)^3 ≠ (n^3 + (n+1)^3) := by
  intro H
  have eq1 : (n + 2 : ℕ) ^ 3 = n^3 + (n + 1 : ℕ) ^ 3 := by
    omega
  by_cases h2 : n ≤ 5
  · -- n ≤ 5
    interval_cases n <;> omega
  · -- n > 5, so n ≥ 6
    have h3 : n ≥ 6 := by
      omega
    have eq2 : (n + 2 : ℕ) ^ 3 < (n ^ 3 + (n + 1 : ℕ) ^ 3) := by
      nlinarith [sq_nonneg ((n : ℕ) : ℤ), sq_nonneg ((n + 1 : ℕ) : ℤ), 
          sq_nonneg ((n + 2 : ℕ) : ℤ),
          sq_nonneg ((n: ℤ) - 4 : ℤ), sq_nonneg ((n + 1 : ℤ) - 4 : ℤ), sq_nonneg ((n + 2 : ℤ) - 4 : ℤ),
          sq_nonneg ((n: ℤ) - 4: ℤ), sq_nonneg ((n + 1: ℤ) - 4: ℤ), sq_nonneg ((n + 2: ℤ) - 4: ℤ),
          sq_nonneg ((n: ℤ) - 0 : ℤ), sq_nonneg ((n + 1: ℤ) - 0 : ℤ), sq_nonneg ((n + 2: ℤ) - 0 : ℤ),
          mul_pos (show (0 : ℕ) < n by linarith) (show (0 : ℕ) < n by linarith)
        ]
    linarith [eq1, eq2]