import Mathlib

/- What are the coordinates of the point on the line $5x-9y=42$ such that the $x$ and $y$ coordinates are the additive inverses of each other? Express your answer as an ordered pair. -/
theorem algebra_21706 {x y : ℝ} (h : 5 * x - 9 * y = 42) (h' : x = -y) :
    (x, y) = (3, -3) := by
  -- substitute h' into h, and we can solve y=-3
  have: y = -3 := by
    rw [h'] at h; simp at h
    linarith [h]
  -- thus x = 3
  rw [this] at h'; simp at h'
  -- so x=3, y = -3
  rw [this, h']