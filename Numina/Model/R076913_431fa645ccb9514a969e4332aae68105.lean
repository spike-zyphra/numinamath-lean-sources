import Mathlib

open Real
open scoped BigOperators

theorem algebra_137031 (a : EuclideanSpace ℝ (Fin 3)) (ha : a = ![6, -2, -3]) :
    ‖a‖ = sqrt (6^2 + (-2)^2 + (-3)^2) ∧
    cos (arccos (6 / sqrt (6^2 + (-2)^2 + (-3)^2))) = 6 / 7 ∧
    cos (arccos (-2 / sqrt (6^2 + (-2)^2 + (-3)^2))) = -2 / 7 ∧
    cos (arccos (-3 / sqrt (6^2 + (-2)^2 + (-3)^2))) = -3 / 7 := by
  constructor
  · -- Show that the norm of a is √(6² + (-2)² + (-3)²).
    rw [ha]
    simp [Fin.sum_univ_three, EuclideanSpace.norm_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    all_goals norm_num
  constructor
  · -- Compute cos (arccos (6 / sqrt (6^2 + (-2)^2 + (-3)^2)))
    have h1 : sqrt ((6^2 + (-2)^2 + (-3)^2 : ℝ)) = 7 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    -- Check 6/7 is in domain of arccos
    have h3 : (6 / 7 : ℝ) ≤ 1 := by norm_num
    have h4 : (-1 : ℝ) ≤ (6 / 7 : ℝ) := by norm_num
    apply cos_arccos
    all_goals linarith
  constructor
  · -- Compute cos (arccos (-2 / sqrt (6^2 + (-2)^2 + (-3)^2)))
    have h1 : sqrt ((6^2 + (-2)^2 + (-3)^2 : ℝ)) = 7 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    -- Check -2/7 is in domain of arccos
    have h3 : (-2 / 7 : ℝ) ≤ 1 := by norm_num
    have h4 : (-1 : ℝ) ≤ (-2 / 7 : ℝ) := by norm_num
    apply cos_arccos
    all_goals linarith
  · -- Compute cos (arccos (-3 / sqrt (6^2 + (-2)^2 + (-3)^2)))
    have h1 : sqrt ((6^2 + (-2)^2 + (-3)^2 : ℝ)) = 7 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    -- Check -3/7 is in domain of arccos
    have h3 : (-3 / 7 : ℝ) ≤ 1 := by norm_num
    have h4 : (-1 : ℝ) ≤ (-3 / 7 : ℝ) := by norm_num
    apply cos_arccos
    all_goals linarith