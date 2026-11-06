import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_185092 {k : ℝ} (hk : k ≠ 0) :
    deriv (λ t => k * sin t + sin (k * t)) 0 / deriv (λ t => k * cos t + cos (k * t)) 0 = 0 := by
  have h1 : deriv (λ t => k * sin t + sin (k * t)) 0 = 2 * k := by
    simp [deriv_add, deriv_mul, deriv_id'', mul_comm k, differentiableAt_sin]
    all_goals field_simp [hk]
    <;> ring_nf <;> simp [hk] <;> ring
  have h2 : deriv (λ t => k * cos t + cos (k * t)) 0 = 0 := by
    simp [deriv_add, deriv_mul, deriv_id'', mul_comm k, differentiableAt_cos]
    all_goals field_simp [hk]
    <;> ring_nf <;> simp [hk] <;> ring
  rw [h1, h2]
  norm_num
  all_goals ring