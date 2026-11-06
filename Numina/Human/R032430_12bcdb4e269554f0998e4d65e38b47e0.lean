import Mathlib

/- Find all triplets of strictly positive integers $(x, y, z)$ such that

$$
(x+y)^{2}+3 x+y+1=z^{2} .
$$ -/
theorem number_theory_145378 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : (x + y)^2 + 3 * x + y + 1 = z^2) :
    (x, y, z) = (x, x, 2 * x + 1) := by
  -- First we prove that y must equal x
  have h2 : y = x := by
    -- Restate the equation with z^2 on the left side
    have h3 : z^2 = (x + y) ^ 2 + 3 * x + y + 1 := by linarith
    -- Prove that z must be greater than x + y
    have h4 : z > x + y := by
      nlinarith [sq_nonneg (z - (x + y)), sq_nonneg (x - y), sq_nonneg (z - (2 * x + 1))]
    -- Prove that z must be less than x + y + 2
    have h5 : z < x + y + 2 := by
      nlinarith [sq_nonneg (z - (x + y + 2)), sq_nonneg (x - y), sq_nonneg (z - (2 * x + 1))]
    -- Since z is an integer and x + y < z < x + y + 2, z must equal x + y + 1
    have h6 : z = x + y + 1 := by
      omega
    -- Substitute z = x + y + 1 into the original equation
    rw [h6] at h3
    -- Simplify the equation using ring normalization
    ring_nf at h3
    -- Solve for y = x using non-linear arithmetic
    nlinarith
  -- Now we prove that z = 2x + 1
  have h3 : z = 2 * x + 1 := by
    -- Substitute y = x into the original equation
    rw [h2] at h
    -- Solve for z using non-linear arithmetic
    nlinarith [sq_nonneg (z - (2 * x + 1))]
  -- Combine the results to form the final solution
  exact Prod.ext rfl (Prod.ext h2 h3)
