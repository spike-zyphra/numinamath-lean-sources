import Mathlib

/-For what value of $k$ does the line represented by the equation $-\frac{1}{2}-2kx = 5y$ contain the point $\left(\frac{1}{4},-6\right)$?-/
theorem algebra_15041 (k : ℝ) (h : -1/2 - 2*k*(1/4) = 5*(-6)) : k = 59 := by
-- This is a straightforward simplification
  apply_fun (fun x => x + (1:ℝ)/2) at h
  ring_nf at h; field_simp at h; assumption