import Mathlib

theorem number_theory_5919 (x : ℤ) (hx : x^3 = 29791) : x = 31 := by
  have h1 : x^3 - 29791 = 0 := by
    rw [show x^3 = 29791 by linarith [hx]]
    all_goals
      norm_num

  have h2 : x ≤ 31 := by
    nlinarith [sq_nonneg (x - 31 : ℤ), sq_nonneg (x + 31 : ℤ),
        sq_nonneg (x ^ 2 - 961 : ℤ), sq_nonneg (x - 31 : ℤ), sq_nonneg (x + 31 : ℤ),
          sq_nonneg ((x - 31) * (x + 31) : ℤ), sq_nonneg (x ^ 2 - 961 : ℤ), sq_nonneg (x - 31 : ℤ)]
  have h3 : x ≥ 31 := by
    nlinarith [sq_nonneg (x - 31 : ℤ), sq_nonneg (x + 31 : ℤ),
        sq_nonneg (x ^ 2 - 961 : ℤ), sq_nonneg (x - 31 : ℤ), sq_nonneg (x + 31 : ℤ),
          sq_nonneg ((x - 31) * (x + 31) : ℤ), sq_nonneg (x ^ 2 - 961 : ℤ), sq_nonneg (x - 31 : ℤ)]
  have h4 : x = 31 := by
    linarith
  exact h4