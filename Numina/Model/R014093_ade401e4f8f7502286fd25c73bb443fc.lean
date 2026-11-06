import Mathlib

theorem number_theory_269657 {n : ℕ} (hn : n^2 = (2 * n + 1) * (2 * n + 3) * (2 * n + 5) * (2 * n + 7)) :
    n^2 = 9 := by
  have h1 : n ≤ 3 := by
    by_contra h
    push_neg at h
    have h2 : (2 * n + 1) * (2 * n + 3) * (2 * n + 5) * (2 * n + 7) > n^2 := by
      nlinarith [sq_nonneg (n ^ 2 : ℤ), sq_nonneg ((2 * n + 1) * (2 * n + 7) - (2 * n + 3) * (2 * n + 5) : ℤ), 
          sq_nonneg ((2 * n + 1) - (2 * n + 7) : ℤ), sq_nonneg ((2 * n + 3) - (2 * n + 5) : ℤ), 
          sq_nonneg (n : ℤ), sq_nonneg ((2 * n) : ℤ)]
    nlinarith
  interval_cases n <;> omega