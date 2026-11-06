import Mathlib

theorem algebra_321449 (f : ℝ → ℝ) (h : ∀ x, 2*f (x^2 + x) + f (x^2 - 3*x + 2) = 9*x^2 - 3*x - 6) :
    f 60 = 176 := by

  have eq1 := h ((-1 + Real.sqrt 241) / 2)
  have eq2 := h ((-1 - Real.sqrt 241) / 2)
  have eq3 := h ((3 + Real.sqrt 241) / 2)
  have eq4 := h ((3 - Real.sqrt 241) / 2)
  ring_nf at eq1 eq2 eq3 eq4
  norm_num [Real.sqrt_pos.mpr, Real.sq_sqrt] at eq1 eq2 eq3 eq4 ⊢
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (241 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (241 : ℝ) by norm_num)]