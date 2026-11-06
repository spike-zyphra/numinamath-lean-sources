import Mathlib

open Complex

/-In the Cartesian plane, a line segment with midpoint $(2020,11)$ has one endpoint at $(a, 0)$ and the other endpoint on the line $y=x$. Compute $a$.-/
theorem geometry_610193 {a : ℝ} {A B : ℂ} (hmid : (A + B) / 2 = 2020 + 11 * I)
  (hA : A = a) (hB : B.re = B.im) : a = 4018 := by
-- Rewrite `hmid` by `Complex.ext_iff`, then the goal follows from `linarith`
  simp [Complex.ext_iff, hA] at hmid; linarith