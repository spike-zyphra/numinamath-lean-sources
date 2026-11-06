import Mathlib

/- The line $ax+(a+1)y=a+2$ passes through the point $(4,-8)$. Find $a$. -/
theorem algebra_14380 {a : ℝ} (h : (4, -8) ∈ { (x, y) | a * x + (a + 1) * y = a + 2 }) :
    a = -2 := by
  simp at h
  linarith
