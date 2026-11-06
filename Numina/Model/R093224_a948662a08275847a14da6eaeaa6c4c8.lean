import Mathlib

open Real Set
open scoped BigOperators

/- Let real numbers $x$, $y$ satisfy $\begin{cases}x \leqslant y \\ y \leqslant 6-2x \\ x \geqslant 1 \end{cases}$, vector $\overrightarrow{a}=(2x-y,m)$, $\overrightarrow{b}=(-1,1)$. If $\overrightarrow{a}//\overrightarrow{b}$, then the minimum value of the real number $m$ is ___          ___. -/
theorem algebra_12312 (x y : ℝ) (hx : 1 ≤ x) (hy : x ≤ y) (h : y ≤ 6 - 2 * x)
  (m : ℝ) (a b : ℝ × ℝ) (ha : a = (2 * x - y, m)) (hb : b = (-1, 1))
  (h1 : a.1 * b.2 = a.2 * b.1) :
  m ≥ -2 := by
  rw [ha, hb] at h1
  simp at h1
  have hm : m = y - 2 * x := by linarith
  linarith [hm, hy, h, hx]