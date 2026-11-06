import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22097 :
  IsLeast {n : ℝ | ∃ x y z, n = 3*x^2 + 12*y^2 + 27*z^2 - 4*x*y - 6*x*z - 12*y*z - 8*y - 24*z} (-14) := by

  constructor
  · -- Show that -14 is in the set.
    use 3 / 2, 1, 5 / 6
    norm_num

  · -- Show that -14 is the least element in the set.
    intro n hn
    rcases hn with ⟨x, y, z, h_eq⟩
    have h1 : -14 ≤ n := by
      rw [h_eq]
      nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y - 1), sq_nonneg (z - 5 / 6), 
                sq_nonneg (x - (2 * y + 3 * z) / 3), sq_nonneg (y - 3 / 4 * z - 3 / 8), sq_nonneg (z - 5 / 6),
                sq_nonneg (3 * x - 2 * y - 3 * z), sq_nonneg (4 * y - 3 * z - 3 / 4), sq_nonneg (6 * z - 5)]

    linarith