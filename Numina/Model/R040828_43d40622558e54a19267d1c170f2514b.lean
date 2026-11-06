import Mathlib

open Real

theorem algebra_216249 :
    IsLeast {t : ℝ | ∃x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = x * y * z ∧ t = x ^ 2 * (y * z - 1) + y ^ 2 * (z * x - 1) + z ^ 2 * (x * y - 1)} 18 := by
  constructor
  · -- Show 18 is achievable, by setting x=y=z=√3
    use Real.sqrt 3, Real.sqrt 3, Real.sqrt 3
    constructor
    · -- Show x is positive
      positivity
    constructor
    · -- Show y is positive
      positivity
    constructor
    · -- Show z is positive
      positivity
    constructor
    · -- Show the constraint x+y+z=x*y*z is satisfied
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 3 - 0)]
    · -- Show that the function value of 18 is attained
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 - 0)]
  · -- Show that 18 is the least element in the image
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - 3), sq_nonneg (y * z - 3), sq_nonneg (z * x - 3),
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
      ]