import Mathlib
/- Suppose that $a$ and $b$ are real numbers such that the line $y=a x+b$ intersects the graph of $y=x^{2}$ at two distinct points $A$ and $B$. If the coordinates of the midpoint of $A B$ are $(5,101)$, compute $a+b$. -/
theorem algebra_610629 (a b x1 x2 y1 y2 : ℝ) (h1 : y1 = a * x1 + b) (h2 : y2 = a * x2 + b) (h3 : y1 = x1 ^ 2) (h4 : y2 = x2 ^ 2) (h5 : (x1 + x2) / 2 = 5) (h6 : (y1 + y2) / 2 = 101) (h7 : x1 ≠ x2 ∨ y1 ≠ y2) : a + b = 61:= by
  -- Using linear arithmetic to show that a*(x1+x2) + 2b equals y1+y2
  have h8 : a * (x1 + x2) + 2 * b = (y1 + y2):= by linarith
  -- Simplify x1 + x2 = 10 from the midpoint x-coordinate
  replace h5 : x1 + x2 = 10:= by linarith
  -- Simplify y1 + y2 = 202 from the midpoint y-coordinate
  replace h6 : y1 + y2 = 202:= by linarith
  -- Update h8 with the simplified values
  rw [h5, h6] at h8
  -- Express y1 - y2 in terms of a and x-coordinates
  have h9 : y1 - y2 = a * (x1 - x2):= by linarith
  -- Express y1 - y2 in terms of x-coordinates using quadratic formula
  have h10 : y1 - y2 = (x1 - x2) * (x1 + x2):= by linarith
  -- Substitute x1 + x2 = 10 into h10
  rw [h5] at h10
  -- Substitute the quadratic expression into h9
  rw [h10] at h9
  -- Simplify to show (x1 - x2)(a - 10) = 0
  replace h9 : (x1 - x2) * (a - 10) = 0:= by linarith
  -- Case analysis on the hypothesis that points are distinct
  rcases h7 with h7 | h7
  -- Case 1: x1 ≠ x2
  .
    -- Prove x1 - x2 ≠ 0 from the hypothesis
    replace h7 : x1 - x2 ≠ 0:= by exact sub_ne_zero_of_ne h7
    -- Use this fact to simplify h9
    simp [h7] at h9
    -- Complete the proof using linear arithmetic
    linarith
  -- Case 2: y1 ≠ y2
  .
    -- Prove x1 - x2 ≠ 0 by contradiction
    replace h7 : x1 - x2 ≠ 0:= by
      by_contra H
      rw [H] at h10
      simp at h10
      replace h10 : y1 = y2:= by linarith
      trivial
    -- Use this fact to simplify h9
    simp [h7] at h9
    -- Complete the proof using linear arithmetic
    linarith
