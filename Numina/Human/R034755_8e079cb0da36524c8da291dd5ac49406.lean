import Mathlib

/- 10.1. Solve in $\square$ the equation $2020^{x^{2}-2 x}+\frac{x^{2}-2 x}{2020^{x}}=1$. -/
theorem algebra_167114 (x : ℝ) :
    2020^(x^2 - 2 * x) + (x^2 - 2 * x) / 2020^x = 1 ↔ x = 0 ∨ x = 2 := by
  -- one direction is completely trivial
  constructor; swap; rintro (rfl | rfl) <;> norm_num
  -- the quadratic term < 0
  -- so the first term is < 1 and the second term < 0
  -- so the sum cannot be 1
  by_cases hx : x^2 - 2 * x < 0
  · intro h
    have hpow : (2020 : ℝ)^(x^2 - 2*x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hx
    have hdiv : (x ^ 2 - 2 * x) / 2020^x < 0 := by apply div_neg_of_neg_of_pos hx (Real.rpow_pos_of_pos (by norm_num) x)
    have := calc
      1 = (2020 : ℝ)^(x^2 - 2*x) + (x ^ 2 - 2 * x) / 2020^x := h.symm
      _ < 1 := by linarith [hpow, hdiv]
    linarith
  push_neg at hx
  rcases hx.lt_or_eq with hxlt | hxe
  -- the quadratic term > 0
  -- so the first term is > 1 and the second term > 0
  -- so the sum cannot be 1
  · intro h
    have hpow : (2020 : ℝ)^(x^2 - 2*x) > 1 := Real.one_lt_rpow (by norm_num) hxlt
    have hdiv : (x ^ 2 - 2 * x) / 2020^x > 0 := by positivity
    have := calc
      1 = (2020 : ℝ)^(x^2 - 2*x) + (x ^ 2 - 2 * x) / 2020^x := h.symm
      _ > 1 := by linarith [hpow, hdiv]
    linarith
  · rw [hxe]
    intro h
    rw [show x^2 - 2 * x = x * (x - 2) by ring] at hxe
    rcases zero_eq_mul.mp hxe with rfl | h2
    left; norm_num
    right; linarith [h2]