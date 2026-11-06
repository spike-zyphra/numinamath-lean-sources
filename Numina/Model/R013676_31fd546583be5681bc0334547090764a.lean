import Mathlib

theorem algebra_6367 {f : ℝ → ℝ} (h : ∀ x, f (x^2 + x) + 2 * f (x^2 - 3 * x + 2) = 9 * x^2 - 15 * x) :
    f 2016 = 6044 := by
  have eq1 := h ( (3 + Real.sqrt 8065) / 2 )
  have eq2 := h ( (3 - Real.sqrt 8065) / 2 )
  have eq3 := h ( (-1 + Real.sqrt 8065) / 2 )
  have eq4 := h ( (-1 - Real.sqrt 8065) / 2 )
  ring_nf at eq1 eq2 eq3 eq4
  norm_num [Real.sqrt_pos.mpr] at eq1 eq2 eq3 eq4
  nlinarith [ Real.sqrt_pos.mpr (show (8065 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (8065 : ℝ) ≥ 0 by norm_num) ]