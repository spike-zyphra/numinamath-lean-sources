import Mathlib

/- How many six-inch by six-inch square tiles are needed to cover a three-foot by two-foot rectangular section of floor? -/
theorem algebra_21605 (r : ℝ × ℝ) (hr : r = (3, 2)) :
    (r.1 * 12 / 6) * (r.2 * 12 / 6) = 24 := by
    -- subst r
    simp [hr]
    -- trivial
    ring_nf
