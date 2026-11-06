import Mathlib
open Real Set

/- Given the function $f(x) = \sqrt{2}\sin(x + \frac{π}{4})$, where $x \in [0,π]$, determine the interval on which the function $f(x)$ is monotonically increasing. -/
theorem algebra_9078 {f : ℝ → ℝ} (hf : f = λ x => √2 * sin (x + π / 4)) :
    StrictMonoOn f (Icc 0 (π / 4)) ∧ StrictAntiOn f (Icc (π / 4) π) := by

  -- Note on the formulation of the problem:
  -- f(x) := √2 * sin(x + π/4) is strictly increasing on the interval [0, π/4] and strictly decreasing on the interval [π/4, π]
  -- Thus, the interval on which f(x) is monotonically increasing is [0, π/4]

  -- Expand the definition of f(x) = √2 * sin(x + π/4)
  rw [hf]
  -- Split the goal into two and simplify the expressions
  constructor <;> intro x hx y hy hxy <;> simp at *
  . -- When x < y ∈ [0, π/4]
    -- x + π/4 < y + π/4 ∈ [-π/2, π/2]
    -- Thus sin(x + π/4) < sin(y + π/4)
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;>
    linarith
  . -- When x < y ∈ [π/4, π]
    -- Rewrite sin(x + π/4) as sin(π - (π/4 - x)) and the same for y
    conv =>
      congr <;> rw [← Real.sin_pi_sub]
    -- π - (π/4 - x) > π - (π/4 - y) ∈ [-π/2, π/2]
    -- Thus sin(π - (π/4 - x)) > sin(π - (π/4 - y))
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;>
    linarith
