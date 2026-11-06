import Mathlib

open Real

theorem calculus_5876 {f : ℝ → ℝ} (hf : f = fun x => (x - 1) * (x ^ 2 + 2) ^ 3) :
    deriv f = fun x => (x ^ 2 + 2) ^ 2 * (7 * x ^ 2 - 6 * x + 2) := by
  rw [hf]
  funext x
  simp [deriv_mul, deriv_sub, deriv_pow, deriv_id'', mul_comm, mul_assoc, add_assoc, pow_three, mul_assoc]
  all_goals ring_nf <;> field_simp <;> ring
  all_goals ring_nf
  <;> field_simp
  <;> ring