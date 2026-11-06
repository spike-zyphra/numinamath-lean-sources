import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13014 : IsLeast {x | ∃ t : ℝ, x = t ^ 4 + 2 * t ^ 3 + 3 * t ^ 2 + 4 * t + 5} 3 := by
  constructor
  · -- Show that 3 is in the set {x | ∃ t : ℝ, x = t ^ 4 + 2 * t ^ 3 + 3 * t ^ 2 + 4 * t + 5}
    use -1
    norm_num
  · -- Show that 3 is the least of the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    nlinarith [sq_nonneg (t ^ 2 + t), sq_nonneg (t + 1), sq_nonneg (t ^ 2 - 1), sq_nonneg (t * 1), sq_nonneg ((t + 1) * (t * 1)), sq_nonneg (t ^ 2 + 1), sq_nonneg (t ^2 -1 *1), sq_nonneg ((t ^ 2 + t) * (t ^2 + t)), sq_nonneg (((t + 1) ) * (t^2 + t)), sq_nonneg (t ^ 2 * 1), sq_nonneg (t *1), sq_nonneg ((t ^ 2 + t * (t ^2))), sq_nonneg (t * (t ^ 2) * (t ^2)), sq_nonneg ((t * 1) * (t ^ 4 *1))]