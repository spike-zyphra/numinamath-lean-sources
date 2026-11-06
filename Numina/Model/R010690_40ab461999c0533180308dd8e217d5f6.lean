import Mathlib

theorem algebra_9193 {f : ℝ → ℝ} (hf : f = fun x => Real.exp x * Real.sin x) :
    deriv f = fun x => Real.exp x * (Real.sin x + Real.cos x) := by
  rw [hf]
  funext x
  simp [deriv_mul, Real.differentiableAt_exp, Real.differentiableAt_sin]
  all_goals ring
  all_goals simp [Real.differentiableAt_exp, Real.differentiableAt_sin]
  all_goals ring