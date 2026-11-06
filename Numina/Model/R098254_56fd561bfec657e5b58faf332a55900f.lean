import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_94501 :
  IsLeast {y : ℝ | ∃ x : ℝ, x ≥ 0 ∧ y = (4 * x ^ 2 + 8 * x + 13) / (6 * (1 + x))} 2 := by
  constructor
  · -- Show that 2 is in the set
    use 1 / 2
    constructor
    · norm_num
    · norm_num
  · -- Show that 2 is the smallest element in the set
    intro y hy
    rcases hy with ⟨x, hx, hy⟩
    have h1 : 4 * x ^ 2 + 8 * x + 13 ≥ 12 * (1 + x) := by
      nlinarith [sq_nonneg (2 * x - 1)]
    have h2 : 6 * (1 + x) > 0 := by 
      positivity
    have h3 : (4 * x ^ 2 + 8 * x + 13) / (6 * (1 + x)) ≥ (12 * (1 + x)) / (6 * (1 + x)) := by
      apply (div_le_div_right h2).mpr
      linarith
    have h4 : (12 * (1 + x)) / (6 * (1 + x)) = 2 := by
      have h5 : 1 + x ≠ 0 := by linarith
      field_simp [h5]
      <;> ring
      <;> nlinarith
    have h5 : (4 * x ^ 2 + 8 * x + 13) / (6 * (1 + x)) ≥ 2 := by
      linarith [h3, h4]
    linarith [hy, h5]