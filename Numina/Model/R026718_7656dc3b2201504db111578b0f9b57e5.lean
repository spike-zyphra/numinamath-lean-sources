import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_6044 :
  IsGreatest {t : ℝ | ∃ x y z, t = 6*x - 3*y - 8*z ∧ 2*x^2 + 3*y^2 + 4*z^2 = 1} (Real.sqrt 37) := by
  constructor
  · -- Show that √37 is in the set
    use 3 * Real.sqrt 37 / 37, -Real.sqrt 37 / 37, -2 * Real.sqrt 37 / 37
    constructor
    · -- Show that 6x - 3y - 8z = √37
      field_simp
      ring_nf
      <;> norm_num
    · -- Show that 2x² + 3y² + 4z² = 1
      nlinarith [Real.sqrt_nonneg 37, Real.sq_sqrt (show (0 : ℝ) ≤ 37 by norm_num)]
  · -- Show that √37 is greatest
    intro t ht
    rcases ht with ⟨x, y, z, ht_eq, ht_constraint⟩
    nlinarith [sq_nonneg (x - 3 * Real.sqrt 37 / 37), sq_nonneg (y + Real.sqrt 37 / 37), sq_nonneg (z + 2 * Real.sqrt 37 / 37),
          sq_nonneg ((6 : ℝ) * (y + Real.sqrt 37 / 37) + 3 * (x - 3 * Real.sqrt 37 / 37) + 4 * (z + 2 * Real.sqrt 37 / 37)), 
          Real.sqrt_nonneg 37, 
          mul_nonneg (Real.sqrt_nonneg 37) (Real.sqrt_nonneg 37), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 37 by norm_num)]