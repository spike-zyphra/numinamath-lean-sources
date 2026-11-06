import Mathlib

/- Example 7 Given $a+b+c=1$,

$$

\frac{1}{a+1}+\frac{1}{b+3}+\frac{1}{c+5}=0 \text {. }

$$


Find the value of $(a+1)^{2}+(b+3)^{2}+(c+5)^{2}$. -/
theorem algebra_145010 {a b c : ℝ} (h₀ : a + b + c = 1) (ha: a+1 ≠ 0) (hb: b+3 ≠ 0) (hc: c+5 ≠ 0) (h₁ : 1 / (a + 1) + 1 / (b + 3) + 1 / (c + 5) = 0) :
  (a + 1) ^ 2 + (b + 3) ^ 2 + (c + 5) ^ 2 = 100 := by
  -- set x = a+1, y = b+3, z = c+5 for ease of work
  set x := a+1 with ha'
  set y := b+3 with hb'
  set z := c+5 with hc'
  -- prove x +y + z = 10 and xy + yz + zx = 0 from given equations
  have hxyz₁ : x + y + z = 10 := by linarith
  have hxyz₂ : x*y + y*z + z*x = 0 := by calc
    x*y + y*z + z*x = (x*y + y*z + z*x)/(x*y*z) * (x*y*z) := by field_simp
    _ = (1/x + 1/y + 1/z) * (x*y*z) := by congr; field_simp; ring
    _ = 0 := by rw [h₁]; simp
  -- finally expressing target as (x+y+z)^2-2(xy+yz+zx), we get result
  calc
    x^2 + y^2 + z^2 = (x+y+z)^2 - 2*(x*y + y*z + z*x) := by ring
    _ = 100 := by
      rw [hxyz₁, hxyz₂]
      norm_num