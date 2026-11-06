import Mathlib

/- If $725x + 727y = 1500$ and $729x+ 731y = 1508$, what is the value of $x - y$ ? -/
theorem algebra_20127 {x y : ℝ} (h1 : 725 * x + 727 * y = 1500) (h2 : 729 * x + 731 * y = 1508) :
    x - y = -48 := by
  -- substract two equations
  have h3: x+y = 2 := by
    have tt1: 4*(x+y) = (729*x+731*y)-(725*x+727*y) := by ring
    have tt2: 4*(x+y) = 8 := by
      rw [tt1, h1, h2]; ring
    linarith [tt2]
  -- multiply x+y=2 by 725, and substract it from 725x+727y=1500, then y is determined.
  have hy: y = 25 := by
    have tt1: 725*x+727*y = 725*(x+y) + 2*y := by ring
    rw [tt1, h3] at h1
    linarith [h1]
  -- y = 25, x+y = 2, so x = -23
  have hx: x = -23 := by linarith [h3, hy]
  -- subsitute, x-y = -23 - 25 = -48
  rw [hx,hy]; norm_num