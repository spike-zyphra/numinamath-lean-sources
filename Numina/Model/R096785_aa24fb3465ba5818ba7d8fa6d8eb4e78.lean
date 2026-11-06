import Mathlib

open Real

theorem calculus_155656 {f : ℝ → ℝ} (hf : f = fun x => arctan (2 * x)) :
    deriv f = fun x => 2 / (1 + 4 * x ^ 2) := by
  rw [hf]
  funext x
  simp [deriv_mul, deriv_id'', differentiableAt_id', differentiableAt_const, mul_comm, 
    Real.deriv_arctan]
  all_goals
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring