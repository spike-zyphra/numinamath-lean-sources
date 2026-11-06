import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13541 : IsLeast {x | ∃ t : ℝ, x = sin t ^ 2 - 12 * cos t - 37} (-49) := by
  constructor
  · -- Show that -49 is in the set
    use 0
    norm_num
  · -- Show that -49 is the least element
    intro y hy
    rcases hy with ⟨t, ht⟩
    have h1 : sin t ^ 2 + cos t ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq t
    have h2 : sin t ^ 2 = 1 - cos t ^ 2 := by
      linarith [h1]
    nlinarith [sq_nonneg (sin t), sq_nonneg (cos t - 1), Real.cos_le_one t, Real.sin_le_one t, Real.neg_one_le_cos t, Real.neg_one_le_sin t]