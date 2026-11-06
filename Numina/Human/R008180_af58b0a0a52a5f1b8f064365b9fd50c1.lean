import Mathlib
open Real Set

/- The function $f(x)=\log_{2}(x^{2}+x)$, then the interval of monotonic increase for $f(x)$ is \_\_\_\_\_. -/
theorem algebra_9095 {f : ℝ → ℝ} (hf : f = λ x => logb 2 (x^2 + x)) :
    StrictMonoOn f (Set.Ioi 0) := by
  -- Expand the definition of f
  rw [hf]
  intro x hx y hy hxy
  simp at *
  -- Prove x^2 + x and y^2 + y are positive
  have hx1 : x ^ 2 + x > 0 := by nlinarith
  have hy1 : y ^ 2 + y > 0 := by nlinarith
  -- Use strict monotonicity of logb 2
  apply Real.logb_lt_logb <;> (try norm_num) <;> nlinarith
