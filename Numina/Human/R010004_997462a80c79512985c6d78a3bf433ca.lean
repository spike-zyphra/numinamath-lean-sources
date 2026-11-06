import Mathlib

/- An engineer invested $\$10,\!000$ in a six-month savings certificate that paid a simple annual interest rate of $12\%$. After six months, she invested the total value of her investment in another six-month certificate. After six more months, the investment was worth $\$11,\!130$. If the annual interest rate of the second certificate is $r\%,$ then what is $r?$ -/
theorem algebra_12932 (P : ℝ) (hP : P = 10000) (r : ℝ) (hr : r > 0)
    (h : (P * (1 + 12 / 100 / 2) * (1 + r / 100 / 2)) = 11130) :
    r = 10 := by
  subst hP
  ring_nf at h
  linarith
