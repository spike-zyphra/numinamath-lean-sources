import Mathlib

theorem algebra_194009 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1 / 18)
    (h' : a * 40 + b * 20 = 1) :
    1 / a = 45 := by
  have eq1 : b = 1 / 18 - a := by linarith
  rw [eq1] at h'
  -- expand and solve the equation
  -- we get $20a + \frac{10}{9} = 1$ which leads to $a < 0$, but $0 < a$.
  have h6 : a < 0 := by
    nlinarith
  linarith