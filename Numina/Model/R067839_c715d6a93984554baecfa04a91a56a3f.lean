import Mathlib

theorem algebra_597415 (f g : ℝ → ℝ) :
    ∃ x y : ℝ, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧ |x * y - f x - g y| ≥ 1 / 4 := by
  by_contra h
  push_neg at h
  have h1 := h 0 0
  norm_num [Set.mem_Icc] at h1
  have h2 := h 1 1
  norm_num [Set.mem_Icc] at h2
  have h3 := h 0 1
  norm_num [Set.mem_Icc] at h3
  have h4 := h 1 0
  norm_num [Set.mem_Icc] at h4
  cases' abs_lt.mp h1 with h1_neg h1_pos
  cases' abs_lt.mp h2 with h2_neg h2_pos
  cases' abs_lt.mp h3 with h3_neg h3_pos
  cases' abs_lt.mp h4 with h4_neg h4_pos
  all_goals
    linarith