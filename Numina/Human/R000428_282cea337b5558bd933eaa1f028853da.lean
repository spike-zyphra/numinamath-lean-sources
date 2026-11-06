import Mathlib

/-If $\frac{1}{x} + \frac{1}{y} = 3$ and $\frac{1}{x} - \frac{1}{y} = -7$ what is the value of $x + y$? Express your answer as a common fraction.-/
theorem algebra_10523 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 1 / x + 1 / y = 3) (h2 : 1 / x - 1 / y = -7) :
    x + y = -3 / 10 := by
  -- First, we find \[\frac1{x} = \frac12\left(\left(\frac1{x}+\frac1{y}\right)+\left(\frac1{x}-\frac1{y}\right)\right) = \frac12(3+(-7)) = -2.\] Therefore, $x = -\frac12$.
  have hx': 1/x = -2 := by linarith
  have hx : x = -1/2 := by
    rw [show -(1 : ℝ)/2 = (-2)⁻¹ by norm_num, hx'.symm]
    rw [one_div, inv_inv]
  --Similarly, we find \[\frac1{y} = \frac12\left(\left(\frac1{x}+\frac1{y}\right)-\left(\frac1{x}-\frac1{y}\right)\right) = \frac12(3-(-7)) = 5.\] Therefore, $y = \frac15$.
  have hy' : 1/y = 5 := by linarith
  have hy : y = 1/5 := by
    rw [one_div, hy'.symm, one_div, inv_inv]
  -- Our desired sum is \[x+y = -\frac12 + \frac15 = \boxed{-\frac{3}{10}}.\]
  rw [hx, hy]
  linarith
