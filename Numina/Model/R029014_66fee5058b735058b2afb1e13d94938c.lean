import Mathlib

/- Positive real numbers x and y satisfy y^3 = x^2 and (y - x)^2 = 4 * y^2. What is x + y?
(A) 12
(B) 18
(C) 24
(D) 36
(E) 42 -/
#check lt_of_pow_lt_pow_left
theorem algebra_95540 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
(h1 : y^3 = x^2) (h2 : (y - x)^2 = 4 * y^2) : x + y = 36 := by

  have eq1 : x^2 - 2 * x * y - 3 * y^2 = 0 := by
    nlinarith [h2, h1]

  -- Factor the quadratic.
  have eq2 : (x - 3 * y) * (x + y) = 0 := by
    nlinarith [eq1]

  cases' (mul_eq_zero.mp eq2) with h3 h4
  · -- Case h3: x - 3y = 0
    have hx_eq : x = 3 * y := by
      linarith

    rw [hx_eq] at h1
    have hy_eq : y^2 * (y - 9) = 0 := by
      nlinarith

    cases' (mul_eq_zero.mp hy_eq) with hy1 hy2
    · -- Case hy1: y^2 = 0
      have hy0 : y = 0 := by
        nlinarith [hy1]
      nlinarith [hy0, hy]
    · -- Case hy2: y - 9 = 0
      have hy9 : y = 9 := by
        linarith
      have hx9 : x = 27 := by
        rw [show y = 9 by linarith] at hx_eq
        linarith
      linarith [hx9, hy9]
  · -- Case h4: x + y = 0
    nlinarith