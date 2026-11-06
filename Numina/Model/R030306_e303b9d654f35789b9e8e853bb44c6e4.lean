import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_36252 (f g : ℝ → ℝ) :
  ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ |x * y - f x - g y| ≥ 1 / 4 := by
  by_contra h
  push_neg at h
  have h1 := h 0 0 (by norm_num) (by norm_num)
  have h2 := h 0 1 (by norm_num) (by norm_num)
  have h3 := h 1 0 (by norm_num) (by norm_num)
  have h4 := h 1 1 (by norm_num) (by norm_num)
  norm_num [abs_lt] at h1 h2 h3 h4
  all_goals linarith