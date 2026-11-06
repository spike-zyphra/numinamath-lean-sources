import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_310463 (x y z : ℝ) (h : x + y + z = 1) :
    IsLeast {u | ∃ x y z : ℝ, x + y + z = 1 ∧ u = 2*x^2 + 3*y^2 + z^2} (6/11) := by 
  constructor 
  · -- Show that 6/11 is in the set
    use 3/11, 2/11, 6/11
    constructor
    · -- Show that 3/11 + 2/11 + 6/11 = 1
      norm_num
    · -- Show that 6/11 = 2*(3/11)^2 + 3*(2/11)^2 + (6/11)^2
      norm_num
  · -- Show that 6/11 is the least element in the set
    rintro u ⟨x, y, z, h_eq, hu⟩
    have hz : z = 1 - x - y := by linarith
    rw [hz] at hu 
    have h1 : 2 * x ^ 2 + 3 * y ^ 2 + (1 - x - y) ^ 2 ≥ (6 / 11) := by 
      nlinarith [sq_nonneg (x - 3 / 11), sq_nonneg (y - 2 / 11), sq_nonneg ((1 - x - y) - 6 / 11), 
          sq_nonneg (x + y - 3 / 11 - 2 / 11), sq_nonneg (2 * x - 6 / 11), sq_nonneg (2 * y - 4 / 11)]
    linarith [h1, hu]