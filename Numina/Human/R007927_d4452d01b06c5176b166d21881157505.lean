import Mathlib

/- Dave rode 30 miles at 10 miles per hour and 10 miles at 30 miles per hour. What was his average speed, in miles per hour, for the entire ride? -/
theorem algebra_16414 (d1 d2 v1 v2 : ℝ) (h₁ : d1 = 30) (h₂ : d2 = 10) (h₃ : v1 = 10) (h₄ : v2 = 30) :
    (d1 + d2) / (d1 / v1 + d2 / v2) = 12 := by
  subst_vars
  norm_num