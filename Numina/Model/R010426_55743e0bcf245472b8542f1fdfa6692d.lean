import Mathlib

theorem algebra_9009 (x : ℝ) (hx : x^2 - 49 = 0) : x = 7 ∨ x = -7 := by
  have h3 : x^2 - 49 = (x - 7) * (x + 7) := by ring
  rw [h3] at hx
  cases' (mul_eq_zero.mp hx) with h4 h5
  · -- Case $h4 : x - 7 = 0$, then $x = 7$
    left
    linarith
  · -- Case $h5 : x + 7 = 0$, then $x = -7$
    right
    linarith