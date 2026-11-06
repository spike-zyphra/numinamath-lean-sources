import Mathlib

/- When the single digit $D$ is written at the end of the positive two-digit integer $XY$, with tens digit $X$ and ones digit $Y$, the resulting positive three-digit integer $XYD$ is 619 more than the original integer $XY$. What is the value of the three-digit integer $XYD$? -/
theorem number_theory_19314 (X Y D : ℕ) (h0 : X < 10) (h1 : Y < 10) (h2 : D < 10) (h3 : 100 * X + Y * 10 + D = 10 * X + Y + 619) :
100 * X + 10 * Y + D = 687 := by
  -- $6 \leq X \leq 7$
  have Xge : X ≥ 6 := by
    linarith
  have Xle : X ≤ 7 := by
    linarith
  interval_cases X
  · -- If $X = 6$
    -- $7 \leq Y \leq 8$
    have Yle : Y ≥ 7 := by
      linarith
    have Yge : Y ≤ 8 := by
      linarith
    interval_cases Y
    · -- If $Y = 7$
      linarith
    · -- If $Y = 8$
      linarith
  · -- If $X = 7$
    linarith
