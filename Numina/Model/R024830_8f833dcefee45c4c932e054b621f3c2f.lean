import Mathlib

theorem inequalities_179364 {x y : ℝ} (hx : x^3 > y^2) (hy : y^3 > x^2) : x + y > 2 := by
  by_contra h
  push_neg at h
  -- Now $x+y \leq 2$. So $x \leq 2-y$.
  -- Now establishing that $x>0$ and $y>0$.
  have h1 : x > 0 := by
    by_contra h2
    push_neg at h2
    have h3 : x ^ 3 ≤ (0 : ℝ) := by
      have h4 : x ≤ (0 : ℝ) := by linarith
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 0), sq_nonneg (x + 0)]
    have h6 : y ^ 2 ≥ (0 : ℝ) := by
      nlinarith [sq_nonneg y]
    nlinarith
  have h2 : y > 0 := by
    by_contra h3
    push_neg at h3
    have h4 : y ^ 3 ≤ (0 : ℝ) := by
      have h5 : y ≤ (0 : ℝ) := by linarith
      nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y - 0), sq_nonneg (y + 0)]
    have h7 : x ^ 2 ≥ (0 : ℝ) := by
      nlinarith [sq_nonneg x]
    nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), 
          sq_nonneg (x + y - 2), mul_pos (show 0 < x by linarith) (show 0 < y by linarith), 
          mul_pos (show 0 < x by linarith) (show 0 < x by linarith), 
          mul_pos (show 0 < y by linarith) (show 0 < y by linarith)]