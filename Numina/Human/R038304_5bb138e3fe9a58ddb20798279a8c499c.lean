import Mathlib

/- From point $A$, Leigh walked 40 yards south, 60 yards west, 10 yards north, and 20 yards east to point $B$. What is the length, in yards, of $\overline{AB}$? -/
theorem algebra_16643 (A B : ℝ × ℝ)
    (hA : A = (0, 0))
    (hB : B = (20 - 60, 10 - 40)) :
    Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) = 50 := by
  rw [hA, hB]
  norm_num [Real.sqrt_eq_iff_sq_eq]