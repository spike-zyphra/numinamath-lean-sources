import Mathlib

/- If $x$, $y$, and $z$ are positive numbers satisfying \[
x+\frac{1}{y}=4,\ \ \ y+\frac{1}{z}=1,\text{ and }z+\frac{1}{x}=\frac{7}{3},
\]find the value of $xyz$. -/
theorem algebra_10283 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + 1 / y = 4) (h2 : y + 1 / z = 1) (h3 : z + 1 / x = 7 / 3) :
    x * y * z = 1 := by
  -- notice that (x+1/y)(y+1/z)(z+1/x)=xyz+(x+1/y)+(y+1/z)+(z+1/x)+1/(xyz)
  have eq1: (x+1/y)*(y+1/z)*(z+1/x) = x*y*z + (x+1/y) + (y+1/z) + (z+1/x) + 1/(x*y*z) := by
    field_simp;ring
  -- x+1/y=4, y+1/z=1, z+1/x=7/3, substitute to the equation.
  have eq2: x*y*z + 1/ (x*y*z) = 2 := by
    rw [h1,h2,h3] at eq1
    have ht1: x*y*z + 4 + 1 + 7 / 3 + 1/(x*y*z) = 22/3 + (x*y*z + 1/(x*y*z)) := by ring
    have ht2: 4*1*(7/3:ℝ) = 22/3 + 2 := by
      field_simp; norm_num
    rw [ht1, ht2] at eq1
    have ht3: (2:ℝ) = 22/3 + 2 - 22/3 := by ring
    rw [ht3, eq1]; ring
  -- xyz + 1/(xyz) = 2, view xyz as a whole, suppose u=xyz. solve the equation about u, we can get u=1.
  let u := x*y*z
  have u_def: u = x*y*z := rfl
  have equ: (u-1)*(u-1) = 0 := by
    rw [← u_def] at eq2
    have unez: u ≠ 0 := by
      by_contra! hc
      rw [hc] at eq2; norm_num at eq2
    have ht1:2*u = u^2+1 := by
      rw [← eq2]; field_simp [unez]; ring
    have ht2: (u-1)*(u-1) = u^2+1 - 2*u := by ring
    rw [ht2, ht1]; simp
  have ueq1: u = 1 := by
    have: u-1 = 0 := by
      have: u-1=0 ∨ u-1=0 := mul_eq_zero.mp equ
      tauto
    rw [← add_zero 1, ← this]; simp
  -- therefore, xyz=u=1.
  rwa [u_def] at ueq1