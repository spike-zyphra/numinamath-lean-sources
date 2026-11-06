import Mathlib

theorem algebra_9379 (f : ℝ → ℝ) (hf : f = fun x => x * Real.sin x + Real.cos x) :
    deriv f = fun x => x * Real.cos x := by
  rw [hf]
  funext x
  simp [deriv_add, deriv_mul, deriv_id'', Real.deriv_sin, Real.deriv_cos]
  all_goals ring