import Mathlib

theorem negated_inequalities_68819 (x y z : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z)
    (hsum : x + y + z = 3) :
    (Real.sqrt x + Real.sqrt y + Real.sqrt z ≥ x * y + y * z + x * z) := by

  have h1 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
  have h2 : Real.sqrt y ≥ 0 := Real.sqrt_nonneg y
  have h3 : Real.sqrt z ≥ 0 := Real.sqrt_nonneg z

  have h4 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have h5 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have h6 : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz
  
  nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt y - 1), sq_nonneg (Real.sqrt z - 1),
            mul_nonneg h1 h2,
            mul_nonneg h1 h3,
            mul_nonneg h2 h3,
            sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]