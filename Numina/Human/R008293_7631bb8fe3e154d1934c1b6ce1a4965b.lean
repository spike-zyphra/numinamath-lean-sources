import Mathlib

/- The equation $x^2 - ax - 3a = 0$ has one root equal to -2. Find its other root.-/
theorem algebra_9428 {a : ℝ} (h : (-2)^2 - a * (-2) - 3 * a = 0) :
    (6)^2 - a * 6 - 3 * a = 0 := by
  -- Let the two roots of the equation be $x_1$ and $x_2$.
  -- According to the problem, one of the roots is $x_1 = -2$.
  -- We can use Vieta's formulas, which relate the roots of a polynomial to its coefficients.
  -- For a quadratic equation $x^2 + bx + c = 0$,
  -- the sum and product of the roots are given by $x_1 + x_2 = -b$ and $x_1x_2 = c$, respectively.
  --In our case, $-ax$ is the term corresponding to $bx$ and $-3a$ to $c$.
  set x : ℝ := -2
  rw [pow_two, sub_eq_add_neg] at h
  -- Therefore, we have:
  -- 1. The sum of the roots: $x_1 + x_2 = a$.
  -- 2. The product of the roots: $x_1x_2 = -3a$.
  obtain ⟨y, hy, hsum, hmul⟩ := vieta_formula_quadratic h
  -- Now, we substitute $x_1 = -2$ into the formulas:
  -- 1. Sum of roots: $-2 + x_2 = a$, so $x_2 = a + 2$.
  -- 2. Product of roots: $-2 \cdot x_2 = -3a$, and using $x_2 = a + 2$, we get $-2(a + 2) = -3a$.
  have hy1 : y = a + 2 := by linear_combination hsum
  have hy2 : 2*y = 3*a := by linear_combination -hmul
  rw [hy1] at hy2
  -- Solving for $a$, we get:
  -- \begin{align*}
  -- -2a - 4 &= -3a, \\
  -- a &= 4.
  -- \end{align*}
  have ha : a = 4 := by linear_combination -hy2
  -- Now, we can find $x_2$ by substituting $a$ back into the expression we found for $x_2$:
  -- \begin{align*}
  -- x_2 &= a + 2, \\
  -- x_2 &= 4 + 2, \\
  -- x_2 &= 6.
  -- \end{align*}
  norm_num [ha] at hy1
  rw [hy1] at hy
  -- Therefore, the other root of the equation is $\boxed{6}$.
  linear_combination hy
