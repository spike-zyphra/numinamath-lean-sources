import Mathlib

/- While standing in line to buy concert tickets, Kit moved 60 feet closer to the ticket window over a period of 30 minutes. At this rate, how many minutes will it take her to move the remaining 70 yards to the ticket window? -/
theorem algebra_15690 (x : ℝ) (h : x = 60 / 30) :
    (70 * 3 / x) = 105 := by norm_num [h]