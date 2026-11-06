import Mathlib

/- A driver travels for 2 hours at 60 miles per hour, during which her car gets 30 miles per gallon of gasoline. She is paid 0.50$ per mile,and her only expense is gasoline at 2.00$ per gallon. What is her net rate of pay, in dollars per hour, after this expense?
(A) 20(B) 22(C) 24(D) 25(E) 26 -/
theorem algebra_93623 (x : ℝ) (h : 2 * 60 = 30 * x) (hx : x > 0) :
(2 * 60 * (0.50:ℚ) - 2 * 60 / 30 * 2.00) / 2 = 26 := by ring_nf
--the thesis is "amount she get paid"-"amount she pays for gasoline" / "time traveled in hours"