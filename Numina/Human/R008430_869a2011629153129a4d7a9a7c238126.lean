import Mathlib

/- Given the non-negative real numbers $x$ and $y$ that satisfy the constraints:
$$
\begin{cases}
x+y-3 \leq 0 \\
2x+y-4 \geq 0
\end{cases}
$$
find the maximum value of $z=2x+3y$.-/
theorem algebra_9298 : IsGreatest {z : ℝ | ∃ x y, z = 2 * x + 3 * y ∧ 0 ≤ x ∧ 0 ≤ y ∧
      x + y - 3 ≤ 0 ∧ 0 ≤ 2 * x + y - 4} 8 := by
  constructor
  -- If x=1,y=2 then z=8.
  . use 1, 2
    norm_num
  -- We can write z as a linear combination of x+y and -(2x+y) : $z=4(x+y)+(-(2x+y))$.
  rintro z ⟨x, y, hz, _, _, h1, h2⟩
  -- Notice that x+y≤3 and
  have : x + y ≤ 3 := by linarith
  -- -(2x+y)≤4 .
  have : -(2 * x + y) ≤ -4 := by linarith
  -- It's obvious that z≤8 .
  have : (x + y) * 4 + (-(2 * x + y)) ≤ 8 := by linarith
  convert this
  rw [hz]
  ring
