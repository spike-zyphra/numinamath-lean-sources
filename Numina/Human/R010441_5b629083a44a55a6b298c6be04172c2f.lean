import Mathlib

/- Suppose that the values of $x$, $y$, and $z$ are given by  \[x=-\frac{2}{3} \qquad y=\frac{5}{7} \qquad z=-\frac{11}{13}.\]What is $\frac{xy}{z}$? -/
theorem algebra_21890 {x y z : ℝ} (hx : x = -2/3) (hy : y = 5/7) (hz : z = -11/13) : x * y / z = 130/231 := by 
  rw [hx, hy, hz]
  ring