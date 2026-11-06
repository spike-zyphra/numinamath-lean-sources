import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_13526 :
  IsLeast {y : ℝ | ∃ x, y = (x ^ 2 + 7) / Real.sqrt (x ^ 2 + 3)} 4 := by
  constructor
  · -- Show that 4 is in the set
    use 1
    have h1 : Real.sqrt (1 ^ 2 + 3) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    norm_num
  · -- Show that 4 is the least
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h2 : (x ^ 2 + 7) / Real.sqrt (x ^ 2 + 3) ≥ (4 : ℝ) := by
      have h3 : Real.sqrt (x ^ 2 + 3) ≥ 0 := by positivity
      have h4 : (x ^ 2 + 7) ≥ 4 * Real.sqrt (x ^ 2 + 3) := by
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 3),
          Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 3 by nlinarith),
          sq_nonneg (x ^ 2 - 1),
          sq_nonneg (Real.sqrt (x ^ 2 + 3) - 2)]
      have h5 : (x ^ 2 + 7 : ℝ) ≥ (4 * Real.sqrt (x ^ 2 + 3)) := by linarith
      have h6 : (x ^ 2 + 7) / Real.sqrt (x ^ 2 + 3) ≥ (4 : ℝ) := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    linarith [h2, hx]