import Mathlib

/- One day, I decide to run to the park. On the way there, I run at a rate of $x^2$ miles per hour for $3$ hours. On the way back, I take the same path and jog at a slower rate of $16 - 4x$ miles per hour so that it takes me $4$ hours to get home. Given that $x > 0$, what is $x$? Express your answer as a common fraction. -/
theorem algebra_20429 (x : ℝ) (hx : x > 0) (h : 3 * x ^ 2 = 4 * (16 - 4 * x)) :
    x = 8 / 3 := by
  -- distance that travel to park and travel back home are the same distance
  -- so x = vt = 3 * x^2 = 4 * (16-x)
  -- solve the equation, x is determined. 
  nlinarith [h]