import Mathlib

open Real

theorem calculus_131359 {y : ℝ → ℝ} (hy : y = fun x => -x * cos x + 3 * x) :
    ∀ x, x * deriv y x = y x + x ^ 2 * sin x := by
  intro x
  have h1 : deriv y x = -cos x + x * sin x + 3 := by
    rw [hy]
    simp [deriv_add, deriv_mul, deriv_id'', mul_comm]
    all_goals try field_simp [differentiableAt_cos, differentiableAt_id']
    all_goals try ring
  rw [h1]
  simp [hy]
  all_goals try ring