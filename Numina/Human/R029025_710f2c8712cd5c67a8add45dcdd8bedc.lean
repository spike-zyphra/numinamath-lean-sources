import Mathlib


/- 84. (1) Let $a, b, c$ and $x, y, z$ be real numbers, prove:
$$\begin{array}{l}
a x+b y+c z+\sqrt{\left(a^{2}+b^{2}+c^{2}\right)\left(x^{2}+y^{2}+z^{2}\right)} \geqslant \\
\frac{2}{3}(a+b+c)(x+y+z)
\end{array}$$
(1989 Ukrainian Mathematical Olympiad Problem) -/
theorem inequalities_600747 (a b c x y z : ℝ) :
    a * x + b * y + c * z + Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)) ≥
    2 / 3 * (a + b + c) * (x + y + z) := by

  -- move ax+by+cz to right side, it suffices to prove √... ≥ 1/3 ...
  suffices √((a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2))
    ≥ 1/3 * ( a*(2*y+2*z-x) + b*(2*z+2*x-y) +c*(2*x+2*y-z) ) by
    linarith only [this]
  suffices a*(2*y+2*z-x) + b*(2*z+2*x-y) +c*(2*x+2*y-z) ≤
    3 * √((a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)) by
    linarith only [this]

  -- use cauchy-schwarz inequality
  have: a*(2*y+2*z-x) + b*(2*z+2*x-y) +c*(2*x+2*y-z) ≤
    √(a^2+b^2+c^2) * √( (2*y+2*z-x)^2 + (2*z+2*x-y)^2 +(2*x+2*y-z)^2 ) := by
    let f : ℕ → ℝ := fun i =>
      match i with
      | 0 => a
      | 1 => b
      | 2 => c
      | n+3 => 0
    let g : ℕ → ℝ := fun i =>
      match i with
      | 0 => (2*y+2*z-x)
      | 1 => (2*z+2*x-y)
      | 2 => (2*x+2*y-z)
      | n+3 => 0
    have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range 3) f g
    simp only [Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, f, g] at this
    exact this
  refine this.trans (le_of_eq ?_)

  -- simplify
  have h1: 0 ≤ a^2+b^2+c^2 := by
    linarith only [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have h2: (3:ℝ) = √(3^2) := by
    rw [Real.sqrt_sq (by norm_num)]
  rw [← Real.sqrt_mul h1, h2, ← Real.sqrt_mul (by norm_num)]
  congr 1
  ring