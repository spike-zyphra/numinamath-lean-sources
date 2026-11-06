import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_600297 (f g : ℝ → ℝ) :
  ∃ x1 x2 : ℝ, 0 ≤ x1 ∧ x1 ≤ 1 ∧ 0 ≤ x2 ∧ x2 ≤ 1 ∧
  |x1 * x2 - f x1 - g x2| ≥ 1 / 4 := by
  by_contra h
  push_neg at h

  have h1 := h 0 0
  have h2 := h 0 1
  have h3 := h 1 0
  have h4 := h 1 1
  norm_num at h1 h2 h3 h4
  cases' abs_lt.mp h1 with h1_neg h1_pos
  cases' abs_lt.mp h2 with h2_neg h2_pos
  cases' abs_lt.mp h3 with h3_neg h3_pos
  cases' abs_lt.mp h4 with h4_neg h4_pos
  all_goals
    linarith