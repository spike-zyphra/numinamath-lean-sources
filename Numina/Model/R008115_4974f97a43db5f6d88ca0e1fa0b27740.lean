import Mathlib
theorem algebra_9425 {x : ℝ} (hx : x^2 - 4 * x - 7 = 0) :
    x = 2 + Real.sqrt 11 ∨ x = 2 - Real.sqrt 11 := by
  have h : x^2 - 4 * x - 7 = (x - (2 + Real.sqrt 11)) * (x - (2 - Real.sqrt 11)) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith [Real.sqrt_nonneg 11]
  rw [h] at hx
  cases' (mul_eq_zero.mp hx) with h1 h2
  · -- Case h1: $x - (2 + \sqrt{11}) = 0$
    left
    linarith
  · -- Case h2: $x - (2 - \sqrt{11}) = 0$
    right
    linarith