import Mathlib
/- Example 17 (Adapted Question, 1999.02.18) Let \( x, y, z, w \in \mathbf{R}^{+} \), and \( x y z w \geqslant 1 \), then
$$\begin{array}{l}
\frac{x}{1+x+x y+x y z}+\frac{y}{1+y+y z+y z w}+\frac{z}{1+z+z x+z w x}+ \\
\frac{w}{1+w+w x+w x y} \leqslant 1
\end{array}$$

Equality in (30) holds if and only if \( x y z w = 1 \). -/
theorem algebra_599280 (x y z w : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0) (h : x * y * z * w ≥ 1) : x / (1 + x + x * y + x * y * z) + y / (1 + y + y * z + y * z * w) + z / (1 + z + z * w + z * w * x) + w / (1 + w + w * x + w * x * y) ≤ 1 ∧ (x / (1 + x + x * y + x * y * z) + y / (1 + y + y * z + y * z * w) + z / (1 + z + z * w + z * w * x) + w / (1 + w + w * x + w * x * y) = 1 ↔ x * y * z * w = 1):= by
  -- The key insight: express 1 minus the sum as a product involving (x*y*z*w - 1)
  have h1 : 1 - (x / (1 + x + x * y + x * y * z) + y / (1 + y + y * z + y * z * w) + z / (1 + z + z * w + z * w * x) + w / (1 + w + w * x + w * x * y)) = (x * y * z * w - 1) * (1 / (1 + x + x * y + x * y * z) * (y / (1 + y + y * z + y * z * w) + z * x / (1 + z + z * w + z * w * x) + (x * y * z * w - 1) / ((1 + z + z * w + z * w * x) * (1 + w + w * x + w * x * y)))):= by
    -- Verify that the sum of all terms in the first denominator equals 1
    have h1 : 1 / (1 + x + x * y + x * y * z) + x / (1 + x + x * y + x * y * z) + x * y / (1 + x + x * y + x * y * z) + x * y * z / (1 + x + x * y + x * y * z) = 1:= by field_simp
    -- Algebraic manipulation of terms to express differences in terms of (x*y*z*w - 1)
    have h2 : x * y / (1 + x + x * y + x * y * z) - y / (1 + y + y * z + y * z * w) = (x * y * z * w - 1) * (y / ((1 + x + x * y + x * y * z) * (1 + y + y * z + y * z * w))):= by field_simp ; ring_nf
    have h3 : x * y * z / (1 + x + x * y + x * y * z) - z / (1 + z + z * w + z * w * x) = (x * y * z * w - 1) * (z * (x + 1) / ((1 + x + x * y + x * y * z) * (1 + z + z * w + z * w * x))):= by field_simp ; ring_nf
    have h4 : 1 / (1 + x + x * y + x * y * z) - w / (1 + w + w * x + w * x * y) = (x * y * z * w - 1) * (-1 / ((1 + x + x * y + x * y * z) * (1 + w + w * x + w * x * y))):= by field_simp ; ring_nf
    -- Combine the previous results to express 1 minus the sum in terms of (x*y*z*w - 1)
    rw [show 1 - (x / (1 + x + x * y + x * y * z) + y / (1 + y + y * z + y * z * w) + z / (1 + z + z * w + z * w * x) + w / (1 + w + w * x + w * x * y)) = (x  * y * z * w - 1) * (y / ((1 + x + x * y + x * y * z) * (1 + y + y * z + y * z * w)) + z * (x + 1) / ((1 + x + x * y + x * y * z) * (1 + z + z * w + z * w * x)) + -1 / ((1 + x + x * y + x * y * z) * (1 + w + w * x + w * x * y))) by linarith]
    clear h1 h2 h3 h4
    -- Further algebraic manipulations to simplify the expression
    suffices y / ((1 + x + x * y + x * y * z) * (1 + y + y * z + y * z * w)) + z * (x + 1) / ((1 + x + x * y + x * y * z) * (1 + z + z * w + z * w * x)) + -1 / ((1 + x + x * y + x * y * z) * (1 + w + w * x + w * x * y)) = 1 / (1 + x + x * y + x * y * z) * (y / (1 + y + y * z + y * z * w) + z * x / (1 + z + z * w + z * w * x) + (x * y * z * w - 1) / ((1 + z + z * w + z * w * x) * (1 + w + w * x + w * x * y))) by rw [this]
    rw [show y / ((1 + x + x * y + x * y * z) * (1 + y + y * z + y * z * w)) = 1 / (1 + x + x * y + x * y * z) * (y / (1 + y + y * z + y * z * w)) by field_simp]
    rw [show z * (x + 1) / ((1 + x + x * y + x * y * z) * (1 + z + z * w + z * w * x)) = 1 / (1 + x + x * y + x * y * z) * (z * (x + 1) / (1 + z + z * w + z * w * x)) by field_simp]
    rw [show -1 / ((1 + x + x * y + x * y * z) * (1 + w + w * x + w * x * y)) = 1 / (1 + x + x * y + x * y * z) * (-1 / (1 + w + w * x + w * x * y)) by field_simp]
    rw [show 1 / (1 + x + x * y + x * y * z) * (y / (1 + y + y * z + y * z * w)) + 1 / (1 + x + x * y + x * y * z) * (z * (x + 1) / (1 + z + z * w + z * w * x)) + 1 / (1 + x + x * y + x * y * z) * (-1 / (1 + w + w * x + w * x * y)) = 1 / (1 + x + x * y + x * y * z) * (y / (1 + y + y * z + y * z * w) + z * (x + 1) / (1 + z + z * w + z * w * x) + -1 / (1 + w + w * x + w * x * y)) by ring]
    suffices y / (1 + y + y * z + y * z * w) + z * (x + 1) / (1 + z + z * w + z * w * x) + -1 / (1 + w + w * x + w * x * y) = y / (1 + y + y * z + y * z * w) + z * x / (1 + z + z * w + z * w * x) + (x * y * z * w - 1) / ((1 + z + z * w + z * w * x) * (1 + w + w * x + w * x * y)) by rw [this]
    rw [show z * (x + 1) / (1 + z + z * w + z * w * x) = z * x / (1 + z + z * w + z * w * x) + z / (1 + z + z * w + z * w * x) by field_simp ; linarith]
    suffices z / (1 + z + z * w + z * w * x) + -1 / (1 + w + w * x + w * x * y) = (x * y * z * w - 1) / ((1 + z + z * w + z * w * x) * (1 + w + w * x + w * x * y)) by linarith
    field_simp
    ring_nf

  -- Construct the conjunction for the theorem statement
  constructor
  -- First part: prove the inequality
  .
    suffices 1 - (x / (1 + x + x * y + x * y * z) + y / (1 + y + y * z + y * z * w) + z / (1 + z + z * w + z * w * x) +
    w / (1 + w + w * x + w * x * y)) ≥ 0 by linarith
    rw [h1]
    replace h : x * y * z * w - 1 ≥ 0:= by linarith
    positivity
  -- Second part: prove the equality condition (iff)
  .
    constructor
    -- Forward direction: if the sum equals 1, then x*y*z*w = 1
    .
      intro h2
      replace h : x * y * z * w - 1 ≥ 0:= by linarith
      replace h2 : 1 - (x / (1 + x + x * y + x * y * z) + y / (1 + y + y * z + y * z * w) + z / (1 + z + z * w + z * w * x) +
      w / (1 + w + w * x + w * x * y)) = 0:= by linarith
      rw [h1] at h2
      have h3 : 1 / (1 + x + x * y + x * y * z) * (y / (1 + y + y * z + y * z * w) + z * x / (1 + z + z * w + z * w * x) +
      (x * y * z * w - 1) / ((1 + z + z * w + z * w * x) * (1 + w + w * x + w * x * y))) ≠ 0:= by positivity
      set t:= 1 / (1 + x + x * y + x * y * z) * (y / (1 + y + y * z + y * z * w) + z * x / (1 + z + z * w + z * w * x) +
      (x * y * z * w - 1) / ((1 + z + z * w + z * w * x) * (1 + w + w * x + w * x * y)))
      clear_value t
      simp [h3] at h2
      linarith
    -- Reverse direction: if x*y*z*w = 1, then the sum equals 1
    .
      intro h2
      suffices 1 - (x / (1 + x + x * y + x * y * z) + y / (1 + y + y * z + y * z * w) + z / (1 + z + z * w + z * w * x) +
      w / (1 + w + w * x + w * x * y)) = 0 by linarith
      rw [h1, h2]
      simp
