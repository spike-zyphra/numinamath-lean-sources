import Mathlib

/- The unknown real numbers $x, y, z$ satisfy the equations

$$
\frac{x+y}{1+z}=\frac{1-z+z^{2}}{x^{2}-x y+y^{2}} ; \quad \frac{x-y}{3-z}=\frac{9+3 z+z^{2}}{x^{2}+x y+y^{2}}
$$

Find $x$. -/
theorem algebra_611052{x y z: ℝ}
  (eq1: (x+y)/(1+z) = (1-z+z^2)/(x^2-x*y+y^2))
  (eq1_den_ne_zero: 1+z ≠ 0 ∧ x^2-x*y+y^2 ≠ 0)
  (eq2: (x-y)/(3-z) = (9+3*z+z^2)/(x^2+x*y+y^2))
  (eq2_den_ne_zero: 3-z ≠ 0 ∧ x^2+x*y+y^2 ≠ 0):
  x = 14^(1/3:ℝ) := by
  -- cross-multiplying in both equations
  replace eq1: x^3+y^3 = 1 + z^3 := by
    rw [div_eq_div_iff eq1_den_ne_zero.left eq1_den_ne_zero.right] at eq1
    nlinarith [eq1]
  replace eq2: x^3-y^3 = 27 - z^3 := by
    rw [div_eq_div_iff eq2_den_ne_zero.left eq2_den_ne_zero.right] at eq2
    nlinarith [eq2]
  -- add these two equations.
  have eq3: x^3 = (14^(1/3:ℝ))^3 := by
    -- add two equations, 2x^3 = 28.
    have h1: 2*x^3 = 28 := by
      have: 2*x^3 = x^3+y^3 + (x^3-y^3) := by ring
      rw [this, eq1, eq2]
      ring
    -- 14^1/3 ^ 3 = 14.
    have h2: ((14:ℝ)^(1/3:ℝ))^3 = 14 := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      norm_num
    rw [h2]
    linarith [h1]
  have: 0 ≤ (14:ℝ)^(1/3:ℝ) := Real.rpow_nonneg (by norm_num) _
  -- x^3 = 14, so x = 14^(1/3).
  apply (pow_left_inj₀ ?_ this (by norm_num)).mp eq3
  replace := pow_nonneg this 3
  rw [← eq3] at this
  apply (Odd.pow_nonneg_iff (Nat.odd_iff.mpr rfl)).mp this