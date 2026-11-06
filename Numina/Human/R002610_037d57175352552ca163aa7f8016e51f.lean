import Mathlib

open Real Set
open scoped BigOperators
/--
A set $S$ of points in the $xy$-plane is symmetric about the origin, both coordinate axes, and the line $y=x$. If $(2,3)$ is in $S$, what is the smallest number of points in $S$?

$\mathrm{(A) \ } 1\qquad \mathrm{(B) \ } 2\qquad \mathrm{(C) \ } 4\qquad \mathrm{(D) \ } 8\qquad \mathrm{(E) \ } 16$
-/
theorem geometry_96306 {S : Set (ℝ × ℝ)}
(hS : let x := 2; let y := 3; S = {(x, y), (-x, -y), (-x, y), (x, -y), (y, x), (-y, -x), (-y, x), (y, -x)}) :
S.encard = 8 := by
  simp only [hS]
  (repeat rw [Set.encard_insert_of_not_mem]) <;> try norm_num