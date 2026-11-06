import Mathlib

/- If \(\left(r+\frac{1}{r}\right)^{2}=3\), then \(r^{3}+\frac{1}{r^{3}}\) equals:
(A) 1
(B) 2
(C) 0
(D) 3
(E) 6
(3rd Annual High School Mathematics Examination, 1952)-/
theorem algebra_4024 {r : ℚ} (hr : r ≠ 0) (h : (r+1/r)^2=3) : r^3+1/r^3=0 := by
  -- the identity of sum of two cubes
  have : r^3+(1/r)^3=(r+1/r)*(r^2-r*(1/r)+1/r^2) := by ring
  -- use above identiy to rewrite `r^3+1/r^3`
  rw [show 1/r^3 = (1/r)^3 by ring, this]
  rw [← sub_eq_zero] at h
  ring_nf at h
  -- use `r*r⁻¹=1` to simplify
  simp [Rat.mul_inv_cancel r hr] at h ⊢
  -- as `r≠0`, `r+r⁻¹` cannot be `0`
  right
  -- draw a conclusion by substitude h to target
  rw [← h]
  ring
