import Mathlib

/- The equation $y = -16t^2 - 60t + 54$ describes the height (in feet) of a ball thrown downward at 60 feet per second from a height of 54 feet from the ground, where $t$ represents time, measured in seconds. In how many seconds will the ball hit the ground? Express your answer as a decimal rounded to the nearest hundredth.-/
theorem algebra_19892 (t : ℝ) (ht : -16*t^2-60*t+54=0) (htpos : 0 < t) :
    t=0.75 := by
  -- Setting $y$ to zero, we find the following: \begin{align*}
  -- 0& = -16t^2 - 60t + 54\\
  -- & = 16t^2 + 60t - 54\\
  -- & = 8t^2 + 30t - 27\\
  -- & = (4t-3)(2t+9)\\
  have : 2 * (4 * t - 3) * (2 * t + 9) = 0 := by linear_combination -ht
  apply_fun (2⁻¹ * ·) at this
  simp at this
  rcases this with h | h
  swap
  . -- As $t$ must be positive,
    linarith
  -- we can see that $t = \frac{3}{4} = \boxed{0.75}.$
  rw [sub_eq_zero] at h
  apply_fun (4⁻¹ * ·) at h
  simp at h
  convert h
  norm_num
