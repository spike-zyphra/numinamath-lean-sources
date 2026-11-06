import Mathlib

/- The reals $x, y, z$ satisfy $x \neq 1, y \neq 1, x \neq y$, and $\left(y z-x^{2}\right) /(1-x)=\left(x z-y^{2}\right) /(1-y)$. Show that $\left(y x-x^{2}\right) /(1-x)=x+y+z$. -/
theorem algebra_604746 {x y z : ℝ} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (h : (y * z - x ^ 2) / (1 - x) = (x * z - y ^ 2) / (1 - y)) :
    (y * z - x ^ 2) / (1 - x) = x + y + z := by
  -- We have 1 - x ≠ 0, 1 - y ≠ 0, and x - y ≠ 0.
  replace hx : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  replace hy : 1 - y ≠ 0 := sub_ne_zero.mpr hy.symm
  rw [← sub_ne_zero] at hxy
  -- Cancel the denominators.
  field_simp at *
  -- Factorize the equation.
  replace h : (x - y) * (-x - y + x * y - z + x * z + y * z) = 0 := by linear_combination h
  -- Cancel the factor (x - y).
  simp [hxy] at h
  linear_combination h
