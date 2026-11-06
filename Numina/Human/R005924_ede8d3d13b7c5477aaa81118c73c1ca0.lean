import Mathlib
/- Compute $\sqrt[ 4]{5508^{3}+5625^{3}+5742^{3}}$, given that it is an integer. -/
theorem algebra_610741 (k : ℤ) (h : ((5508 : ℝ) ^ 3 + (5625 : ℝ) ^ 3 + (5742 : ℝ) ^ 3) ^ (1 / 4 : ℝ) = k) : k = 855:= by
  -- Step 1: Simplify the sum of cubes to 855⁴ using ring tactic
  rw [show (5508 : ℝ) ^ 3 + (5625 : ℝ) ^ 3 + (5742 : ℝ) ^ 3 = 855 ^ (4 : ℝ) by ring] at h
  -- Step 2: Use the property that (x^a)^b = x^(ab) for the fourth root
  rw [Eq.symm (Real.rpow_mul (by linarith) 4 (1 / 4))] at h
  -- Step 3: Simplify the expression using simp tactic
  simp at h
  -- Step 4: Convert to rational numbers
  rify
  -- Step 5: Solve using linear arithmetic
  linarith
