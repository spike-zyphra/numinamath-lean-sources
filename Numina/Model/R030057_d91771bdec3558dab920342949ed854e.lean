import Mathlib

open Real Set
open scoped Real

theorem algebra_158713 {α β : ℝ} (h : sin (α + β) = 0) :
    cos (α + 2 * β) = cos α := by
  have h1 : cos (α + 2 * β) = cos (α + β) * cos β - sin (α + β) * sin β := by
    rw [show α + 2 * β = (α + β) + β by ring]
    rw [cos_add]
  have h2 : cos α = cos (α + β) * cos β + sin (α + β) * sin β := by
    rw [show α = (α + β) - β by ring]
    rw [cos_sub]
    all_goals ring
  rw [h1, h2]
  simp [h]