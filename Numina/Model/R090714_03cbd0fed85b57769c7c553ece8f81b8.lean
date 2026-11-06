import Mathlib

theorem inequalities_205342 (f : ℝ → ℝ) (hf : f = fun x => x^12 - x^9 + x^4 - x + 1) :
    ∀ x, f x > 0 := by
  intro x
  have hfx : f x = x^12 - x^9 + x^4 - x + 1 := by rw [hf]
  rw [hfx]
  nlinarith [sq_nonneg (x^6), sq_nonneg (x^3 - x^2), sq_nonneg (x^3 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x^2 - x), sq_nonneg (x - 1), sq_nonneg (x^5 - x^2), sq_nonneg (x^5 - x), sq_nonneg (x^3), sq_nonneg (x^6 - 1), sq_nonneg (x^6 - x^3), sq_nonneg (x^4 - x), sq_nonneg (x^4 - 1), sq_nonneg (x^4 - x^2), sq_nonneg (x^2), sq_nonneg (x), sq_nonneg (x^5 - 1), mul_nonneg (sq_nonneg x) (sq_nonneg (x^5)), mul_nonneg (sq_nonneg x) (sq_nonneg (x^2 -1)), mul_nonneg (sq_nonneg (x^3)) (sq_nonneg (x^3)), sq_nonneg (x^3 - x), sq_nonneg (x^5 + x^4 - x^3), sq_nonneg (x^2 -1), sq_nonneg (x^6 -1), mul_nonneg (sq_nonneg (x^2)) (sq_nonneg (x^2)), mul_nonneg (sq_nonneg x) (sq_nonneg x), sq_nonneg (x^4), sq_nonneg (x^5), sq_nonneg (x^3)]