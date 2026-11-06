import Mathlib.Tactic

/-
PROBLEM:
One dimension of a cube is increased by $1$, another is decreased by $1$, and the third is left unchanged. The volume of the new rectangular solid is $5$ less than that of the cube. What was the volume of the cube?
$\textbf{(A)}\ 8 \qquad \textbf{(B)}\ 27 \qquad \textbf{(C)}\ 64 \qquad \textbf{(D)}\ 125 \qquad \textbf{(E)}\ 216$
-/

theorem alg_1204
  (a : ℝ)
  (diff_vol : a ^ 3 - (a - 1) * a * (a + 1) = 5) :
  a ^ 3 = 125 := by
    -- simplify the equation for the new volume
    have : (a - 1) * a * (a + 1) = a ^ 3 - a := by ring
    rw [this] at diff_vol
    norm_num at diff_vol
    rw [diff_vol]
    norm_num