import Mathlib
/- $$
[ \sqrt{2-\sqrt{3}}(2-\sqrt{3})+\sqrt{2+\sqrt{3}}(2+\sqrt{3})]^{2}=?
$$ -/
theorem algebra_275734 : (√(2 - √3) * (2 - √3) + √(2 + √3) * (2 + √3)) ^ 2 = 54:= by
  -- First, we prove that 2-√3 is non-negative, which is needed for the square root to be well-defined
  have g1 : 2 - √3 ≥ 0:= by
    -- Rewrite 2 as the square root of 4 to help with the comparison
    rw [show (2 : ℝ) = √(2 ^ 2) by field_simp]
    -- Simplify the expression using ring normalization
    ring_nf
    -- Prove that 3 ≤ 4 as a helper fact
    have g1 : (3 : ℝ) ≤ 4:= by linarith
    -- Use the fact that square root preserves ordering to conclude 2-√3 ≥ 0
    linarith only [Real.sqrt_le_sqrt g1]
  -- Normalize the expression using ring operations
  ring_nf
  -- Simplify field expressions
  field_simp
  -- Further normalize with ring operations
  ring_nf
  -- Use the property that √a·√b = √(a·b) to simplify the expression
  rw [show √(2 - √3) * √(2 + √3) = √((2 - √3) * (2 + √3)) by field_simp]
  -- Normalize again
  ring_nf
  -- Further field simplification
  field_simp
  -- Final ring normalization
  ring_nf
  -- Simplify the expression
  simp
  -- Use linear arithmetic to complete the proof
  linarith
