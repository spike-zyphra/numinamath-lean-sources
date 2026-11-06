import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_140825 {u : ℝ → ℝ} (hu : u = λ x => sin (2 * x - 1)) :
    deriv (λ x => (u x)^2) = λ x => 2 * sin (2 * (2 * x - 1)) := by
  rw [hu]
  funext x
  simp [deriv_pow, deriv_mul, deriv_id'', mul_comm, mul_assoc, Real.deriv_sin, mul_add, sub_eq_add_neg]
  all_goals
    ring_nf
    <;> field_simp [Real.sin_sq, Real.cos_sq]
    <;> ring