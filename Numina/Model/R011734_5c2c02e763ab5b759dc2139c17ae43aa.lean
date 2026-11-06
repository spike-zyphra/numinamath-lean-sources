import Mathlib

theorem inequalities_285513 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u + v + w = 2) :
    0 ≤ u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ∧ u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ≤ 1 := by
  have hw_eq : w = 2 - u - v := by linarith
  rw [hw_eq]
  constructor
  · -- Show that the expression is non-negative
    positivity
  · 
    nlinarith [sq_nonneg (u - 1), sq_nonneg (v - 1), sq_nonneg ((2 - u - v) - 1), 
          sq_nonneg (u * v - u * (2 - u - v)), sq_nonneg (u * v - v * (2 - u - v)), 
          sq_nonneg (u * (2 - u - v) - v * (2 - u - v)), 
          mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ v by linarith), 
          mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ 2 - u - v by nlinarith), 
          mul_nonneg (show 0 ≤ 2 - u - v by nlinarith) (show 0 ≤ u by linarith)
        ]