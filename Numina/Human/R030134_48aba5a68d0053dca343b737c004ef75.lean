import Mathlib

/- Given the motion equation of an object is $s=t^2+ \frac{3}{t}$ (where $t$ is time, $s$ is displacement), the velocity of the object at the moment $t=2$ is ______.-/
theorem algebra_9129 {s : ℝ → ℝ} (hs : s = fun t => t ^ 2 + 3 / t) :
    deriv s 2 = 13 / 4 := by
  -- Calculating deriv of s(t)=t^2+3/t.
  rw [hs, deriv_add (differentiableAt_pow 2),
    deriv_div (differentiableAt_const 3) differentiableAt_id' (by norm_num)]
  norm_num
  -- Showing that f(x)=3/x is differentiable at x=2.
  . apply DifferentiableAt.div
    . exact differentiableAt_const 3
    . exact differentiableAt_id'
    . norm_num
