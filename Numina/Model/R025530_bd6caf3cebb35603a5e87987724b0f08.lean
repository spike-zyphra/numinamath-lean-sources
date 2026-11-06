import Mathlib

theorem algebra_261600 (n : ℕ) (h₀ : n > 0) (h₁ : (n - 1) * 36 + 2 = n * (n - 1)) :
    n = 8 := by
  have h2 : n ≤ 37 := by
    by_contra h
    push_neg at h
    have h3 : n > 37 := by linarith
    have h4 : n * (n - 1) > (n - 1) * 36 + 2 := by
      have h5 : n ≥ 38 := by omega
      have h6 : n - 1 ≥ 37 := by omega
      have h7 : n * (n - 1) ≥ n * 37 := by
        nlinarith
      have h8 : (n - 1) * 36 + 2 ≤ n * 37 - 34 := by
        omega
      nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) - 37 : ℤ), sq_nonneg ((n : ℤ) - 19 : ℤ)]
    linarith
  interval_cases n <;> omega