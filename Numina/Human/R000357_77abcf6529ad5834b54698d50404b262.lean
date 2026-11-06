import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

/-The monotonic decreasing interval of the function $y=x\ln x$ is.-/
theorem algebra_9114 {f : ℝ → ℝ} (hf : f = λ x => x * Real.log x) :
MonotoneOn (-f) (Set.Ioo 0 (exp (-1))) := by
-- Apply monotoneOn_of_deriv_nonneg, we only need to prove that
-- the derivative of $-f$ is nonnegative on the interval $(0, e^-1)$
  have hf' : -f = λ x => - (x * Real.log x) := by ext; simp [hf]
  apply monotoneOn_of_deriv_nonneg; apply convex_Ioo
-- Prove that $f$ is continuous
  rw [continuousOn_neg_iff, hf]; rw [ContinuousOn]
  intro x hx; rw [continuousWithinAt_iff_continuousAt]
  have := continuous_mul_log
  rw [continuous_iff_continuousAt] at this; apply this
  rw [mem_nhds_iff_exists_Ioo_subset]; use 0; use rexp (-1)
-- Prove that $f$ is differentiable
  rw [hf', differentiableOn_neg_iff]; rw [DifferentiableOn]
  intro x hx; simp; apply DifferentiableWithinAt.mul
  apply differentiableWithinAt_id; apply DifferentiableWithinAt.log
  apply differentiableWithinAt_id; simp at hx; linarith
  intro x hx; simp at hx
-- In fact, $-f$ has a name "Real.negMulLog" in mathlib and its derivative is already computed,
-- we only need to check that this derivative is nonnegative on the interval $(0, e^-1)$
  have hf'' : -f = Real.negMulLog := by
    rw [Real.negMulLog_def, hf]; ext; simp
  rw [hf'', deriv_negMulLog]; simp; rw [le_neg]; rw [Real.log_le_iff_le_exp]
  linarith; linarith; linarith