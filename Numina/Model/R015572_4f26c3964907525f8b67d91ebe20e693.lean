import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_3177 : (√(-1) = √(√((-1)^2)) ∧ √(√((-1)^2)) = (1 : ℂ) ^ (1 / 4)) ↔
    False := by
  constructor
  · -- Assume the conjunction is true, prove False
    intro h
    rcases h with ⟨h1, h2⟩
    -- Show that h1 is False.
    have h4 : √(-1 : ℝ) = (0 : ℝ) := by
      rw [Real.sqrt_eq_zero']
      all_goals norm_num
    have h5 : √((-1 : ℝ) ^ 2) = (1 : ℝ) := by
      rw [show (-1 : ℝ) ^ 2 = (1 : ℝ) by norm_num]
      rw [Real.sqrt_eq_cases]
      all_goals norm_num
      all_goals norm_num
    have h6 : √(√((-1 : ℝ) ^ 2)) = (1 : ℝ) := by
      rw [h5]
      rw [Real.sqrt_eq_cases]
      all_goals norm_num
      all_goals norm_num
    -- Now rewrite h1 with the computed values.
    rw [h4, h6] at h1
    -- h1 now is 0 = 1, which is false. This leads to a contradiction.
    norm_num at h1
  · -- Assume False, prove the conjunction is true
    intro h
    cases h