import Mathlib

/- 3. Prove that for any $x>\sqrt{2}$ and $y>\sqrt{2}$, we have $x^{4}-x^{3} y+x^{2} y^{2}-x y^{3}+y^{4}>x^{2}+y^{2}$.
(46th Moscow Olympiad) -/
theorem inequalities_100372 (x y : ℝ) (hx : x > Real.sqrt 2) (hy : y > Real.sqrt 2) :
    x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 > x^2 + y^2 := by
  -- convert goal to following form
  suffices (x^2 + y^2) * (1 + x * y) + x^2 * y^2 < (x^2 + y^2)^2 by linarith
  -- first prove 2 < x^2, y^2
  have hx : 2 < x^2 := by
    rw [show 2 = (√2)^2 by simp]
    gcongr
  have hy : 2 < y^2 := by
    rw [show 2 = (√2)^2 by simp]
    gcongr
  -- now use am-gm on x^2, y^2 to prove following
  have : x^2 * y^2 ≤  (x^2 + y^2)^2 / 4 := by
    linarith [show 0 ≤ (x^2 - y^2)^2 by positivity]
  -- then use am-gm on x, y and multiply by (x^2 + y^2) to get following
  have : (x^2 + y^2) * x * y ≤ (x^2 + y^2)^2 / 2 := by
    suffices (x^2 + y^2) * (x * y) ≤ (x^2 + y^2) * ((x^2 + y^2) / 2) by linarith
    gcongr
    linarith [show 0 ≤ (x - y)^2 by positivity]
  -- finally multiply 4 < x^2 + y^2 by x^2 + y^2 to get following
  have : x^2 + y^2 < (x^2 + y^2)^2 / 4 := by
    suffices (x^2 + y^2) * 4 < (x^2 + y^2) * (x^2 + y^2) by linarith
    gcongr
    linarith
  -- adding up last 3 inequality gives target
  linarith