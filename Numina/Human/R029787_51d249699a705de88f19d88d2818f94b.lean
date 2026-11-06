import Mathlib

/- Given that the function $f(x)$ is a decreasing function on the interval $(0, +\infty)$, the relationship between $f(3)$ and $f(2)$ is \_\_\_\_\_\_.-/
theorem algebra_9230 {f : ℝ → ℝ} (hf : StrictAntiOn f (Set.Ioi 0)) :
    f 3 < f 2 := by
  -- It's clear that $f(3) < f(2)$ since $f(x)$ is decreasing function on $(0, +\infty)$.
  apply hf
  all_goals norm_num
