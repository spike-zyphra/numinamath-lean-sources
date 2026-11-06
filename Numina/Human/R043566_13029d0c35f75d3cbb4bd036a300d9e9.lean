import Mathlib

open Complex

/- Given that $a, b$, and $c$ are complex numbers satisfying

$$
\begin{aligned}
a^{2}+a b+b^{2} & =1+i \\
b^{2}+b c+c^{2} & =-2 \\
c^{2}+c a+a^{2} & =1,
\end{aligned}
$$

compute $(a b+b c+c a)^{2}$. (Here, $i=\sqrt{-1}$.) -/
theorem algebra_609219 (a b c : ℂ) (h₁ : a ^ 2 + a * b + b ^ 2 = 1 + I) (h₂ : b ^ 2 + b * c + c ^ 2 = -2) (h₃ : c ^ 2 + c * a + a ^ 2 = 1) :
    (a * b + b * c + c * a) ^ 2 = (-11 - 4 * I) / 3 := by
  -- Let x := b ^ 2 + b * c + c ^ 2, y := c ^ 2 + c * a + a ^ 2, z := a ^ 2 + a * b + b ^ 2,
  -- We have (a * b + b * c + c * a) ^ 2 = (x + y + z) ^ 2 - 2 * (x ^ 2 + y ^ 2 + z ^ 2) / 3.
  have H : (a * b + b * c + c * a) ^ 2 =
    let x := b ^ 2 + b * c + c ^ 2;
    let y := c ^ 2 + c * a + a ^ 2;
    let z := a ^ 2 + a * b + b ^ 2;
    ((x + y + z) ^ 2 - 2 * (x ^ 2 + y ^ 2 + z ^ 2)) / 3 := by ring
  -- Substitute the given equations into the expression.
  rw [H, h₁, h₂, h₃]
  simp
  -- Calculation in complex numbers.
  apply Complex.ext
  all_goals
    simp [sq, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
    norm_num
