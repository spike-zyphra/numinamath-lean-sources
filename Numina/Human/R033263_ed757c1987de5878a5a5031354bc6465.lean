import Mathlib

/- Given that $(-2,3)$ is on the graph of $y=f(x)$, find a point on the graph of $y=f(2x+1)+3$. Express your answer as an ordered pair $(a,b)$ where $a$ and $b$ are real numbers. -/
theorem algebra_22238 {f : ℝ → ℝ} (hf : f (-2) = 3) :
    ∃ (x y : ℝ), y = f (2 * x + 1) + 3 := by
  -- since we only know f(-2), so we should find x such that 2x+1=-2.
  -- solve the equation, x = -3/2
  have h1: 2 * (-3/2:ℝ) + 1 = -2 := by ring
  -- and if x = -3/2, then f(2 x -3/2 + 1) = f(-2) = 3, 3+3=6
  have h2: 6 = f (-2) + 3 := by
    rw [hf]; ring
  -- so (-3/2, 6) is the answer.
  use (-3/2)
  use 6
  rw [h1, h2]