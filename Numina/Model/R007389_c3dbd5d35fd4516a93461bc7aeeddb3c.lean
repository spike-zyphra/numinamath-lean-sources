import Mathlib

theorem algebra_10332 (n : ℕ) (h₀ : n > 0) (h₁ : n^2 + (n+1)^2 + (n+2)^2 = 7805) :
    n^3 + (n+1)^3 + (n+2)^3 = 398259 := by
  have h2 : n = 50 := by
    nlinarith [sq_nonneg (n - 50 : ℤ), sq_nonneg (n - 51 : ℤ), sq_nonneg (n - 52 : ℤ)]
  rw [h2]
  all_goals
  norm_num