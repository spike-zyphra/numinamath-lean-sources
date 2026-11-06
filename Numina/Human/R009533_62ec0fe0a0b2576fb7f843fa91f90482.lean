import Mathlib

/- The doctor has told Cal O'Ree that during his ten weeks of working out at the gym, he can expect each week's weight loss to be
1
%
1% of his weight at the end of the previous week. His weight at the beginning of the workouts is
244
244 pounds. How many pounds does he expect to weigh at the end of the ten weeks? Express your answer to the nearest whole number. -/
theorem algebra_21926 (x : ℝ) (hx : x = 244) :
    round (x * (1 - 1 / 100)^10) = 221 := by
    -- substitute x with 244
    rw [hx, round_eq]
    -- trivial calculation
    norm_num
