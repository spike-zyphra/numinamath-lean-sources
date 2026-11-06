import Mathlib

/- 329. Solve the system of equations:


$$

\left\{\begin{array}{l}
x y^{2}-2 y^{2}+3 x=18 \\
3 x y+5 x-6 y=24
\end{array}\right.

$$
 -/
theorem algebra_188075 {x y : ℝ} (h1 : x * y^2 - 2 * y^2 + 3 * x = 18) 
    (h2 : 3 * x * y + 5 * x - 6 * y = 24) :
    (x, y) = (3, 3) ∨ (x, y) = (75 / 13, -3 / 7) := by 
  --from both equations, factor out (x-2) and substract -6 both sides.
  have eq1 : y ^ 2 * (x - 2) + (3 * x - 6) = 18 - 6 := by ring_nf; linarith
  have eq2 : 3 * y * (x - 2) + (5 * x - 10) = 24 - 10 := by ring_nf; linarith
  --factor aut again (x-2) from the second addend and collect the common (x-2) factor.
  have eq1' : (y ^ 2 + 3) * (x - 2) = 12 := by ring_nf; linarith
  have eq2' : (3 * y + 5) * (x - 2) = 14 := by ring_nf; linarith
  --divide first by second equations and find a second order equation in y
  have : 3 * y + 5 ≠ 0 := by
    by_contra hh
    have : y = - 5 / 3 := by field_simp; linarith
    rw[this] at h2
    ring_nf at h2
    linarith
  have div : (y ^ 2 + 3) / (3 * y + 5) = 12 / 14 := by
    field_simp
    rw[← eq1', ← eq2']
    ring_nf
  have eqsq : 7 * y ^ 2 - 18 * y - 9 = 0 := by
    field_simp at div
    ring_nf
    linarith
  --this gives two solutions y = 3 and y = - 3 / 7
  have mul_r_eq : (y - 3) * (y + 3 / 7) = 0 := by field_simp; ring_nf; linarith
  rw[mul_eq_zero] at mul_r_eq
  obtain r1|r2 := mul_r_eq
  --substitute back in one of the equations to find x
  · have hy : y = 3 := by linarith
    rw[hy] at eq2
    --in the first case x = 3 by linear arithmetic
    have hx : x = 3 := by ring_nf at eq2; linarith
    left
    simp
    exact ⟨hx, hy⟩
    --in the second case x = 3 / 7 by linear arithemtic
  · have hy : y = - 3 / 7 := by linarith
    rw[hy] at eq2
    have hx : x = 75 / 13 := by ring_nf at eq2; linarith
    right
    simp
    exact ⟨hx, hy⟩