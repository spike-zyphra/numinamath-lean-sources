import Mathlib

open Real Set

theorem algebra_20700 :
    IsLeast {t : ℝ | ∃ x y z, t = 2*x^2 + 5*y^2 + 2*z^2 + 4*x*y - 4*y*z - 2*z - 2*x} (-1) := by 
  constructor 
  · -- Show that -1 lies in the set. 
    use 1 / 2, 0, 1 / 2 
    norm_num
  · -- Show that -1 is minimal.
    intro t ht 
    rcases ht with ⟨x, y, z, ht⟩ 
    nlinarith [sq_nonneg (x + y - 1 / 2), sq_nonneg (y), sq_nonneg (z - 1 / 2 - y), sq_nonneg (x - 1 / 2), sq_nonneg (z - 1 / 2), sq_nonneg (2 * y + 1 / 2 - z), sq_nonneg (x + 1 / 2 - z)]