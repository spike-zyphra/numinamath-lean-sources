import Mathlib

theorem algebra_28572 {f : ℝ → ℝ} (h : ∀ x, f (x^2 + x + 3) + 2 * f (x^2 - 3 * x + 5) = 6 * x^2 - 10 * x + 17) :
    f 85 = 167 := by
  have eq1 := h ((-1 + Real.sqrt 329) / 2)
  have eq2 := h ((-1 - Real.sqrt 329) / 2)
  have eq3 := h ((3 + Real.sqrt 329) / 2)
  have eq4 := h ((3 - Real.sqrt 329) / 2)

  ring_nf at eq1 eq2 eq3 eq4
  norm_num [Real.sqrt_mul_self] at eq1 eq2 eq3 eq4
  linarith [eq1, eq2, eq3, eq4]