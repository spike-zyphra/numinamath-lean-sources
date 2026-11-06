import Mathlib

/- Determine all integers $a, b, c$ satisfying the identities:

$$
\begin{gathered}
a+b+c=15 \\
(a-3)^{3}+(b-5)^{3}+(c-7)^{3}=540
\end{gathered}
$$ -/
theorem algebra_605071 {a b c : ℤ} (h₀ : a + b + c = 15) (h₁ : (a - 3) ^ 3 + (b - 5) ^ 3 + (c - 7) ^ 3 = 540) :
    (a - 3) * (b - 5) * (c - 7) = 180 := by {
  -- Solution II: We use the substitution $a-3=x, b-5=y, c-7=z$.
  let x := a - 3
  let y := b - 5
  let z := c - 7

  /-
  Now, equations are transformed to:

  $$ \begin{aligned} x+y+z & =0 \ x^{3}+y^{3}+z^{3} & =540 . \end{aligned} $$
  -/
  have : x + y + z = 0 := by omega
  have sum_cubes : x ^ 3 + y ^ 3 + z ^ 3 = 540 := h₁
  /-
  Substituting $z=-x-y$ in the second equation, we get:

  $$ -3 x y^{2}-3 x^{2} y=540 $$
  -/
  have z_eq_m_x_m_y : z = -x - y := by linarith
  have : -3 * x * y ^ 2 - 3 * x ^ 2 * y = 540 := by {
    rw [z_eq_m_x_m_y] at sum_cubes
    ring_nf at sum_cubes
    convert sum_cubes using 1
    ring
  }
  /-
  or

  $$ x y(x+y)=-180 $$
  -/
  have : x * y * (x + y) = -180 := by {
    qify
    have eq : (-3 * x * y ^ 2 - 3 * x ^ 2 * y : ℚ) = 540 := by norm_cast
    /- not needed
    have : (-3 * (x * y * (x + y)) : ℚ) = 540 := by {
      convert eq using 1
      ring
    }
    -/
    linarith
  }
  /-
  or
  $$ x y z=180 \text {. } $$
  -/
  have : x * y * z = 180 := by {
    have : x * y * (-x - y) = 180 := by linarith
    rwa [z_eq_m_x_m_y]
  }
  /-
  Returning to the starting problem we have:

  $$ (a-3)(b-5)(c-7)=180 $$
  -/
  assumption
}
