import Mathlib

open Real

theorem calculus_155671 {y : ℝ → ℝ} (hy : y = fun x => arctan (x^2)) :
    deriv y = fun x => 2 * x / (1 + x^4) := by
  rw [hy]
  funext x 
  simp [deriv_comp, deriv_pow, deriv_id'', differentiableAt_id', differentiableAt_arctan, mul_comm]
  all_goals 
    field_simp
    <;> ring_nf 
    all_goals 
      field_simp
      <;> ring