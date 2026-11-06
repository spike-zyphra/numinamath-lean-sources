import Mathlib
open Real Set
open scoped Real

theorem algebra_9403 : IsLeast {x | ∃ t : ℝ, x = cos t ^ 2 - 3 * cos t + 2} 0 := by 
  constructor
  · -- Show that 0 belongs to the set.
    use 0
    norm_num [Real.cos_zero]
  · -- Show that 0 is the least element in the set.
    intro x hx
    rcases hx with ⟨t, ht⟩ 
    have h1 : cos t ≥ -1 := by
      nlinarith [Real.cos_sq_add_sin_sq t, Real.sin_sq_le_one t]
    have h2 : cos t ≤ 1 := Real.cos_le_one t
    nlinarith [sq_nonneg (cos t - 1), sq_nonneg (cos t - 2)]