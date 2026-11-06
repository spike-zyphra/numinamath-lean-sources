import Mathlib

theorem algebra_170329 (f : ℝ → ℝ) (hf : f = fun m => m^6 - m^5 + m^4 + m^2 - m + 1) :
    ∀ m : ℝ, f m > 0 := by
  intro m
  rw [hf]
  have h1 : m^6 - m^5 + m^4 + m^2 - m + 1 > 0 := by
    nlinarith [sq_nonneg (m ^ 3 - m ^ 2 / 2), sq_nonneg (m - 1), sq_nonneg (m ^ 2 - m + 1), sq_nonneg (m ^ 4 - m ^ 2 * (m - 1)), sq_nonneg (m ^ 2 - m), sq_nonneg (m ^ 2 + 1), sq_nonneg (m - 1 / 2)]
  simpa using h1