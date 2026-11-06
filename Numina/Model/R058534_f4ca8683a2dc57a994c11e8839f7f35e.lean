import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_325679 (a b : ℝ) (ha : ∀ x ∈ Icc 1 2, |a * x^2 + b * x + a| ≤ x) :
    3 * a + b ≤ 3 := by
  have h1 := ha 1 (by norm_num)
  have h2 := ha 2 (by norm_num)
  have h3 := ha 1.5 (by norm_num)
  norm_num [abs_le] at h1 h2 h3
  -- We derive linear constraints from these and other possible points
  -- We know from our earlier analysis using these points and maximize
  -- The expression 3a + b.
  -- Using the constraints from x=1, 2 and 1.5 to make them strict equalities
  -- Then solving the linear program to get the maximum value 3
  linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, sq_nonneg (a - 1), sq_nonneg (b - 0)]