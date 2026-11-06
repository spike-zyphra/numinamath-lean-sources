import Mathlib

/- Let $a$ and $b$ be the solutions of the equation $2x^2-10x+5=0$. What is the value of $(2a-3)(4b-6)$? -/
theorem algebra_19239 {a b : ℝ} (ha : 2*a^2-10*a+5=0) (hb : 2*b^2-10*b+5=0)
    (hne : a≠b) : (2*a-3)*(4*b-6)=-22 := by 
  apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
  nlinarith