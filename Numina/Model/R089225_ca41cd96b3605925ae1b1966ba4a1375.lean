import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_165434 {u : ℝ → ℝ} (hu : u = λ x => exp (sin x - 2 * x ^ 2))
  (z y : ℝ → ℝ) (hz : z = λ x => sin x) (hy : y = λ x => x ^ 2) :
  deriv u = λ x => exp (sin x - 2 * x ^ 2) * (cos x - 4 * x) := by 
    rw [hu]
    funext x
    simp [deriv_sub, deriv_id'', mul_comm, differentiableAt_exp, differentiableAt_sin]
    all_goals field_simp
    all_goals ring