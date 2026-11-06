import Mathlib

/- You begin with $\frac{1}{2}$ scoop of ice cream.  Since you're hungry, you ask the vendor for $\frac{2}{7}$ more scoops of ice cream.  Then, you eat $\frac{5}{8}$ scoops.  How many scoops of ice cream are left on your cone? -/
theorem algebra_21239 (x : ℝ) (hx : x = 1 / 2 + 2 / 7 - 5 / 8) :
    x = 9 / 56 := by
  linarith