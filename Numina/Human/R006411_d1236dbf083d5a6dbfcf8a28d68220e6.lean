import Mathlib

/-
Let $d$ be an odd positive integer. The four integers $-3d, -d, d, 3d$ form an arithmetic progression of odd integers with common difference $2d$. Show that their product is $(3d^2)^2$.
-/

theorem number_theory_636754 (d:ℤ) (hd: Odd d ∧ 0 < d):
(-(3*d)) * (-d) * d * (3*d) = (3*d^2)^2 := by
  ring