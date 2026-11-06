import Mathlib

/- How many distinct diagonals of a convex hexagon can be drawn?-/

theorem algebra_18749 (n : ℕ) (hn : n = 6) :

    (n * (n - 3)) / 2 = 9 := by
    --From each vertex $V$, we can draw 3 diagonals: one to each vertex that is not $V$ and does not share an edge with $V$.  There are 6 vertices in a hexagon, so we might be tempted to say the answer is $6\times 3 = 18$.  However, note that this counts each diagonal twice, one time for each vertex.  Hence there are $\frac{18}{2} = \boxed{9}$ distinct diagonals in a convex hexagon.
    rw [hn]
    