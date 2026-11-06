import Mathlib

/- 9. (12 points) Car A departs from location A to location B, while at the same time, Car B departs from location B to location A. Car A's speed is 80 kilometers per hour, and Car B's speed is 70 kilometers per hour. Car A stops at an intermediate point C, and 15 minutes later, Car B arrives at point C, at which time Car A resumes its journey. If both cars arrive at their destinations simultaneously, then the distance between A and B is $\qquad$ kilometers. -/
theorem algebra_250753 (d : ℝ) (h : d > 0) (h1 : d / 80 = d / 70 - 15 / 60) :
    d = 140 := by

      --Subject -15/60 in equation h1.
      have h2 : d / 80 - d / 70 = (-15) / 60 := by
        linarith
      --Simplify d/80 - d/70 and show it equals -d/560.
      have h3 : d / 80 - d / 70 = (-d) / 560 := by
        field_simp
        linarith

      --`linarith` closes the goal.
      linarith