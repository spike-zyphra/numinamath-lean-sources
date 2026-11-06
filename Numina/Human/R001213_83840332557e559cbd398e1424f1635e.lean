import Mathlib

/- Dr. Zaius invests $\$10,000$ in a CD with an annual interest rate of $4\%$ that compounds semi-annually (twice a year).  After six months, he rolls over the CD into another CD with an annual interest rate of $5\%$ that also compounds semi-annually.  After six months in the second CD, how much does Dr. Zaius have, in dollars? -/
theorem algebra_21386 {P : ℝ} (hP : P = 10000) (r1 r2 : ℝ)
    (hr1 : r1 = 0.04) (hr2 : r2 = 0.05) : P * (1 + r1 / 2) * (1 + r2 / 2) = 10455 := by subst P r1 r2; norm_num
