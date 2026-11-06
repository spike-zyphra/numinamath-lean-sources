import Mathlib

/- Billy shoots an arrow from 10 feet above the ground. The height of this arrow can be expressed by the equation $h=10-23t-10t^2$, where $t$ is time in seconds since the arrow was shot. If the center of a target is raised 5 feet off the ground, in how many seconds must the arrow reach the target in order for Billy to hit the bulls eye? -/
theorem algebra_21174 (h : ℝ → ℝ) (h_def : h = fun t => 10 - 23 * t - 10 * t ^ 2)
    (target : ℝ) (htarget : target = 5) (t : ℝ) (tpos : t > 0) (ht : h t = target) :
    t = 1 / 5 := by
  simp [h_def, htarget] at ht
  nlinarith
