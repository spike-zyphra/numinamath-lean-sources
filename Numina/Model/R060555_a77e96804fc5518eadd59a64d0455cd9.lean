import Mathlib

open Real Set
open scoped Real

theorem algebra_120502 : ¬ ∀ α β : ℝ, cos (α + β) = cos α + cos β := by 
  intro h
  have h0 := h 0 0 
  norm_num [cos_zero] at h0