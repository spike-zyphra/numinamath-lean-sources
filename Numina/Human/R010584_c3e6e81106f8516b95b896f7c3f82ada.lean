import Mathlib

/- For the regression line equation $\hat{y} = 4.75x + 257$, when $x=28$, the estimated value of $y$ is ______. -/
theorem algebra_9244 (f : ℝ → ℝ) (hf : f = fun x => 4.75 * x + 257) (x : ℝ) (hx : x = 28) : f x = 390 := by
  simp [hf, hx]
  norm_num
