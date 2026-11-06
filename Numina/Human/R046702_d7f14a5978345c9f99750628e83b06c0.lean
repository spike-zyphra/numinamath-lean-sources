import Mathlib
open Real Set

/- The interval of monotonic increase for the function $y=\log_{2}(x^{2}-4x)$ is. -/
theorem algebra_9099 {f : ℝ → ℝ} (hf : f = λ x => logb 2 (x^2 - 4 * x)) :
    MonotoneOn f {x | 4 < x} ∧ AntitoneOn f {x | x < 0} := by
  -- Note on formalization of the problem:
  -- f(x) = log_2(x^2 - 4x) is defined only for x^2 - 4x > 0, i.e., {x | 4 < x} ∪ {x | x < 0}
  -- We will prove that f is monotone on {x | 4 < x} and antitone on {x | x < 0} and thus the increasing interval is {x | 4 < x}
  constructor
  -- Split into two and prove them simultaneously
  all_goals
    intro x hx y hy hxy
    simp [hf] at hx hy ⊢
    -- Prove that x^2 - 4x > 0 and y^2 - 4y > 0
    have h1 : 0 < x^2 - 4 * x := by nlinarith
    have h2 : 0 < y^2 - 4 * y := by nlinarith
    -- Strict monotonicity of log_2
    apply logb_le_logb_of_le (by norm_num) (by linarith)
    nlinarith
