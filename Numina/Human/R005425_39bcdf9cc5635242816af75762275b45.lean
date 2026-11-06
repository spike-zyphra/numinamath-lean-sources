import Mathlib

/- Three positive reals $x, y$, and $z$ are such that

$$
\begin{aligned}
x^{2}+2(y-1)(z-1) & =85 \\
y^{2}+2(z-1)(x-1) & =84 \\
z^{2}+2(x-1)(y-1) & =89
\end{aligned}
$$

Compute $x+y+z$. -/
theorem algebra_608242 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h₁ : x ^ 2 + 2 * (y - 1) * (z - 1) = 85)
    (h₂ : y ^ 2 + 2 * (z - 1) * (x - 1) = 84)
    (h₃ : z ^ 2 + 2 * (x - 1) * (y - 1) = 89) :
    x + y + z = 18 := by
  -- Adding the three equations, we get
  -- x^2 + y^2 + z^2 + 2xy + 2xz + 2yz - 2x - 2y - 2z + 6 = 258
  -- So (x + y + z - 2)^2 = 16^2
  have H : (x + y + z - 2) ^ 2 = 16 ^ 2 := by linear_combination h₁ + h₂ + h₃
  -- Evidently x + y + z - 2 = 16 or -16, but -16 is impossible
  rw [sq_eq_sq_iff_eq_or_eq_neg] at H
  rcases H with H | H <;>
    linarith
