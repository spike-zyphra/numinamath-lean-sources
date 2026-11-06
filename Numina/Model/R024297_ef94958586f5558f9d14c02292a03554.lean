import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_308449 {f : ℝ → ℝ}
  (hf : f = λ x => -x^4 + 4 * x^3 - 2 * x^2 - 2 * x + 13 / 9) :
  ∀ x ∈ Icc 0 1, f x > 0 := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have h1 : f x = -x^4 + 4 * x^3 - 2 * x^2 - 2 * x + 13 / 9 := by
    rw [hf]
  rw [h1]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 0), sq_nonneg (x - 3 / 4), sq_nonneg (x - 1 / 4),
          sq_nonneg (x ^ 2 - x), sq_nonneg ((x - 1 / 2) * (x - 1 / 2)), 
          mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hx1)]