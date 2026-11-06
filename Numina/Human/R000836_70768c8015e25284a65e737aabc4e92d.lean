import Mathlib

/- What is the largest value among $\operatorname{lcm}[12,2],$ $\operatorname{lcm}[12,4],$ $\operatorname{lcm}[12,6],$ $\operatorname{lcm}[12,8],$ $\operatorname{lcm}[12,10],$ and $\operatorname{lcm}[12,12]?$ Express your answer as an integer. -/
theorem algebra_17198 : max (max (max  (lcm 12 2) (lcm 12 4)) (lcm 12 6)) (max (lcm 12 8) (lcm 12 10)) ⊔ (lcm 12 12) = 60 := by
  decide