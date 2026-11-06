import Mathlib

theorem algebra_284148 (f : ℝ → ℝ) (hf : f = fun x => x^12 - x^9 + x^4 - x + 1) :
    ∀ x, f x > 0 := by 
  intro x
  calc
    f x = x^12 - x^9 + x^4 - x + 1 := by rw [hf]
    _ > 0 := by nlinarith [sq_nonneg (x^6 - x^3 / 2 + 1 / 2), sq_nonneg (x^3 - 1),
        sq_nonneg (x^2 - 1), sq_nonneg (x), sq_nonneg (x - 1)]