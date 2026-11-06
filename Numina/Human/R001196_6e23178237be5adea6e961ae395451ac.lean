import Mathlib

/- Melanie ran at $5$ m/s for $400$ meters, then ran at $4$ m/s for the next $800$ meters, and finally ran at $8$ m/s for the final $400$ meters. What was her average speed, in meters per second, for the $1600$ meter run?  Express your answer as an improper fraction. -/
theorem algebra_21066 (v1 v2 v3 d1 d2 d3 : ℝ) (h1 : v1 = 5) (h2 : v2 = 4) (h3 : v3 = 8)
    (hd1 : d1 = 400) (hd2 : d2 = 800) (hd3 : d3 = 400) :
    (d1 + d2 + d3) / (d1 / v1 + d2 / v2 + d3 / v3) = 160 / 33 := by
  subst v1 v2 v3 d1 d2 d3
  norm_num
