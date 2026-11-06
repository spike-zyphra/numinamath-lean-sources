import Mathlib

/- Let $a$ and $b$ be the solutions of the equation $2x^2+6x-14=0$. What is the value of $(2a-3)(4b-6)$? -/
theorem algebra_17241 {a b : ℝ} (ha : 2*a^2+6*a-14=0) (hb : 2*b^2+6*b-14=0)
    (h : a≠b) : (2*a-3)*(4*b-6)=-2 := by
  apply mul_right_cancel₀ (sub_ne_zero.2 h)
  nlinarith