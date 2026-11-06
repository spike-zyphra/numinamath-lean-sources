import Mathlib

theorem algebra_285254 {n : ℕ} (h : n^2 + (n+1)^2 + (n+2)^2 = 8 * (n + (n+1) + (n+2)) + 2) :
    n^2 + (n+1)^2 + (n+2)^2 = 194 := by
        have eq1 : n ≤ 9 := by
            nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 1), sq_nonneg (n + 2)]
        interval_cases n <;> omega