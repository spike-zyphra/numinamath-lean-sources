import Mathlib

/-let x,y,z be non_negative numbers such that x^2+y^2+z^2+x+2y+3z=13/4
Find the mininum value of x+y+z-/
open Real Set
open scoped BigOperators

theorem algebra_207391 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧
    x^2 + y^2 + z^2 + x + 2 * y + 3 * z = 13 / 4 ∧ t = x + y + z} ((-3 + sqrt 22) / 2) := by
  constructor
  · -- Show that (-3 + √22) / 2 belongs to the set
    use 0, 0, (-3 + sqrt 22) / 2
    constructor
    · -- Show x ≥ 0
      norm_num
    constructor
    · -- Show y ≥ 0
      norm_num
    constructor
    · -- Show z ≥ 0
      have h1 : sqrt 22 ≥ 3 := by
        have h2 : (3 : ℝ) ^ 2 < (22 : ℝ) := by norm_num
        have h3 : (3 : ℝ) < sqrt 22 := Real.lt_sqrt_of_sq_lt h2
        linarith
      linarith [Real.sqrt_nonneg 22, h1]
    constructor
    · -- Show that x² + y² + z² + x + 2y + 3z = 13/4
      ring_nf
      have h2 : (sqrt 22) ^ 2 = 22 := Real.sq_sqrt (by norm_num)
      linarith [h2]
    · -- Show that t = x + y + z
      ring
  · -- Show that (-3 + √22) / 2 is a lower bound
    intro t
    rintro ⟨x, y, z, hx, hy, hz, h_eq, ht⟩
    have h : (sqrt 22) ^ 2 = 22 := Real.sq_sqrt (by norm_num)
    -- use the conditions for equality, we put the key terms into nlinarith to prove the result --
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z - (-3 + sqrt 22) / 2), h_eq, Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num), h, ht]