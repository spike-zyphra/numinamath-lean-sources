import Mathlib

theorem algebra_284148 (f : ℝ → ℝ) (hf : f = fun x => x^12 - x^9 + x^4 - x + 1) :
    ∀ x, f x > 0 := by 
  intro x 
  have hfx : f x = x^12 - x^9 + x^4 - x + 1 := by 
    rw [hf]
  rw [hfx]
  nlinarith [sq_nonneg (x^6 - x^4 / 2), sq_nonneg (x^6 - x^3 / 2), sq_nonneg (x^4 - x^2 / 2), sq_nonneg (x^3 - 1 / 2), sq_nonneg (x^2 - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2), sq_nonneg (x^6), sq_nonneg (x^3), sq_nonneg (x^4 - x), sq_nonneg (x^2 - x), sq_nonneg (x^6 - x^3), sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - x), sq_nonneg (x^6 - 1), sq_nonneg (x^3 - 1), sq_nonneg (x^4 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x - 1)]