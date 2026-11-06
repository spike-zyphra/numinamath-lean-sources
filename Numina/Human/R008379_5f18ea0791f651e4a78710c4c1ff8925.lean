import Mathlib

/- The equation $y = -16t^2 + 26t + 105$ describes the height (in feet) of a ball tossed up in the air at 26 feet per second from a height of 105 feet above the ground. In how many seconds will the ball hit the ground? Express your answer as a decimal rounded to the nearest tenth. -/
theorem algebra_21255 (t : ℝ) (ht : t ≥ 0) (h : -16*t^2 + 26*t + 105 = 0) :
    t = 3.5 := by
    -- $-16*t^2 + 26*t + 105 = - (8 * t + 15) * (2 * t - 7)$
    have h1 : -16*t^2 + 26*t + 105 = - (8 * t + 15) * (2 * t - 7) := by
      ring
    rw [h1] at h
    simp only [neg_add_rev, mul_eq_zero] at h
    rcases h with h | h
    -- case $8 * t + 15 = 0$, contradicting to $t \geq 0$
    linarith
    --case $2 * t - 7 = 0$, implying $t = 3.5$
    ring_nf
    linarith
    