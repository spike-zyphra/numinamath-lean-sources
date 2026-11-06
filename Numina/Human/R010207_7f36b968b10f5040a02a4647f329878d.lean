import Mathlib

/- Find $t$ such that $(t,5)$ lies on the line through $(0,3)$ and $(-8,0)$. -/
theorem algebra_10920
    (t : ℝ)
    (h : ∃ x y, x = t ∧ y = 5 ∧ (x - 0) * (0 - 3) = (y - 3) * (-8 - 0)) :
    t = 16 / 3 := by
  -- The slope of the line through $(0,3)$ and $(-8,0)$ is $(0-3)/(-8-0) = 3/8$. If $(t,5)$ is also on this line, then the slope of  the line through $(t,5)$ and $(0,3)$ must also be $3/8$.  Therefore, we must have $$\frac{3-5}{0-t} = \frac{3}{8} \implies \frac{2}{t} = \frac{3}{8} \implies (2)(8) = 3(t) \implies t = \boxed{\frac{16}{3}}.$$
  obtain ⟨x, y, hx, hy, h⟩ := h
  linarith
