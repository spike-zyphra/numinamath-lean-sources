import Mathlib

theorem algebra_325764 {f : ℝ → ℝ}
    (h : ∀ x, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x) :
    f 50 = 146 := by 
  have eq1 := h ((-1 + Real.sqrt 201)/2)
  have eq2 := h ((-1 - Real.sqrt 201)/2)
  have eq3 := h ((3 + Real.sqrt 201)/2)
  have eq4 := h ((3 - Real.sqrt 201)/2)
  ring_nf at eq1 eq2 eq3 eq4 ⊢
  norm_num [Real.sq_sqrt, Real.sqrt_nonneg] at eq1 eq2 eq3 eq4 ⊢
  nlinarith [Real.sqrt_nonneg (201 : ℝ), Real.sq_sqrt (show 0 ≤ (201 : ℝ) by norm_num)]