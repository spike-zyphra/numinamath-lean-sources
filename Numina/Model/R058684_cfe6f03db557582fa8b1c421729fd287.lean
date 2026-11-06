import Mathlib

theorem inequalities_224707 (f : ℝ → ℝ) (hf : f = fun x => x^12 - x^9 + x^4 - x + 1) :
    ∀ x, f x > 0 := by
  intro x
  rw [hf]
  simp
  nlinarith [sq_nonneg (x^6 - x^3 / 2), sq_nonneg (x^3 - 1), sq_nonneg (x^3 + 1), sq_nonneg (x^2 - 1/2), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^4 - x/2), sq_nonneg (x^6 - x/2), sq_nonneg (x^2 - x), sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - 1/2), sq_nonneg (x - 1/2), sq_nonneg (x^3 - 1/2), sq_nonneg (x^3 + 1/2), sq_nonneg (x^9), sq_nonneg (x^8), sq_nonneg (x^4), sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^3 - x), sq_nonneg (x^4 - x^2)]