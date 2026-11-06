import Mathlib

/- A birdbath is designed to overflow so that it will be self-cleaning. Water flows in at the rate of 20 milliliters per minute and drains at the rate of 18 milliliters per minute. Which one of these graphs shows the volume of water in the birdbath during the filling time and continuing into the overflow time?
(A) A(B) B(C) C(D) D(E) E -/
theorem algebra_95129 (t ins outs : ℝ) (ht : t > 0) :
(20 * t - 18 * t) > 0 := by 
--the claim shows that the difference between the water flowing in and out is 2*t>0 which means that the graph is linearly increasing until full capacity.
  linarith