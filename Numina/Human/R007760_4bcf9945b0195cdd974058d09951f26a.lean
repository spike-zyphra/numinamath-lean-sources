import Mathlib

open Real
/--
The point $(-3,2)$ is rotated $90^\circ$ clockwise around the origin to point $B$. Point $B$ is then reflected over the line $x=y$ to point $C$. What are the coordinates of $C$?

$\mathrm{(A)}\ (-3,-2) \qquad \mathrm{(B)}\ (-2,-3) \qquad \mathrm{(C)}\ (2,-3) \qquad \mathrm{(D)}\ (2,3) \qquad \mathrm{(E)}\ (3,2)$
-/

theorem geometry_97049 (P : ℝ × ℝ) (hP : P = (-3, 2)) :
let B := (P.2, -P.1)
let C := (B.2, B.1)
C = (3, 2) := by
  rw [hP]
  norm_num