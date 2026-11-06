import Mathlib

/- Tickets for the football game are \$10 for students and \$15 for non-students. If 3000 fans attend and pay \$36250, how many students went? -/
theorem algebra_85726 (x y : ℕ) (h : x * 10 + y * 15 = 36250) (h' : x + y = 3000) :
    x = 1750 := by
  omega