import Mathlib
open Real Set

/- Determine the interval on which the function $y = \log(-x^2 + 2x)$ is monotonically increasing. -/
theorem algebra_9176 {f : ℝ → ℝ} (hf : f = λ x => log (-x^2 + 2 * x)) :
    StrictMonoOn f (Set.Ioc 0 1) ∧ StrictAntiOn f (Set.Ico 1 2) := by
  -- Note on the formulation of the problem:
  -- The function f(x) = log(-x^2 + 2x) is defined on {x ∈ ℝ | -x^2 + 2x > 0}, which is (0, 2)
  -- f(x) is strictly increasing on the interval (0, 1] and strictly decreasing on the interval [1, 2)
  -- Thus, the interval on which f(x) is monotonically increasing is (0, 1]

  -- Expand the definition of f(x) = log(-x^2 + 2x)
  rw [hf]
  -- Split the goal into two and simplify the expressions
  constructor <;> intro x hx y hy hxy <;> simp at *
  . -- When x < y ∈ (0, 1]
    -- Use the strict monotonicity of log
    apply Real.strictMonoOn_log <;> (try simp) <;> nlinarith
  . -- When x < y ∈ [1, 2)
    -- Use the strict monotonicity of log
    apply Real.strictMonoOn_log <;> (try simp) <;> nlinarith
