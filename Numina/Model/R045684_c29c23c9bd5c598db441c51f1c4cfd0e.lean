import Mathlib

open Real

theorem calculus_139575 {f : ℝ → ℝ} (hf : f = fun x => (1 + x ^ 2) * exp (arctan x)) :
    deriv f = fun x => (2 * x + 1) * exp (arctan x) := by
  rw [hf]
  funext x
  simp [deriv_mul, deriv_add, deriv_pow, deriv_id'', differentiableAt_id, differentiableAt_exp, Real.differentiableAt_arctan, mul_add, mul_comm]
  all_goals
    simp [Real.deriv_arctan, mul_add, mul_comm, mul_assoc, add_mul]
    all_goals 
      field_simp [exp_ne_zero (arctan x)]
      <;> ring_nf
      <;> field_simp [exp_ne_zero (arctan x)]
      all_goals
        ring_nf
        all_goals
          simp [exp_ne_zero]
          all_goals
            ring_nf
            <;> ring