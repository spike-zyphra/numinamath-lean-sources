import Mathlib
/-If $(x - 1) + (x - 2) + (x - 3) + (x - 4) = x$, then what is $x$?-/
theorem algebra_20090 {x : ℝ} (h : x - 1 + x - 2 + x - 3 + x - 4 = x) : x = 10 / 3 := by 
    --The equation $(x - 1) + (x - 2) + (x - 3) + (x - 4) = x$ simplifies to $4x - 10 = x$, so $3x = 10$, which means $x = \boxed{\frac{10}{3}}$.
    ring_nf at h
    have e := congrArg ( fun (t) => ((t) - x + 10 ) / 3) h; simp at e; ring_nf at e
    exact e
    