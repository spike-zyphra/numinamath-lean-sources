import Mathlib

/- A $\emph{convex}$ polygon is a polygon in which every interior angle is less than 180 degrees.  A $\emph{diagonal}$ of a convex polygon is a line segment that connects two non-adjacent vertices.  How many diagonals does a convex polygon with 20 sides have? -/
theorem algebra_14548 {n : ℕ} (hn : n = 20) :
    (n * (n - 3)) / 2 = 170 := by
  subst hn
  rfl